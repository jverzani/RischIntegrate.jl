# ---------------------------------------------------------------------------
# Step EH: e^(ax) R(cos bx, sin bx), not elementary (Rubi 1539-1543: eˣ/(1 + cos x), e^(mx)/sin²x). With E = e^(ibx),
# R is a rational function of E over ℚ(i); by partial fractions R = Σ pₙ Eⁿ + Σ c_{r,k}/(E - r)ᵏ (r ≠ 0 the roots, in
# ℚ(i)), and with s = a/(ib),
#   ∫ e^(ax) Eⁿ = e^(ax) Eⁿ/(a + ibn),    ∫ e^(ax)/(1 - E/r)ᵏ = e^(ax) ₂F₁(k, s; s + 1; E/r)/a
# (Σ (k)ₙ/n! zⁿ e^(ax) Eⁿ/(ib(s + n)) = e^(ax) ₂F₁(k, s; s + 1; z)/a). The integrand is real, so the real part of
# the sum is an antiderivative: e^(ax)/a Re(C ₂F₁(k, iσ; 1 + iσ; ρ e^(iφ))), σ = -a/b, ρ = 1/|r|, φ = bx - arg r,
# printed with `rehyp2f1` and `imhyp2f1` (continuous between the poles of R). The partial fractions are checked
# exactly; a may be a parameter.
# ---------------------------------------------------------------------------
using HypergeometricFunctions: _₂F₁

"""
    rehyp2f1(k, σ, ρ, φ)

Re ₂F₁(k, iσ; 1 + iσ; ρ e^{iφ}) for real σ, ρ, φ (analytic continuation off z ∈ [1, ∞)). RischIntegrate uses it,
with [`imhyp2f1`](@ref), for ∫ e^{ax} R(cos bx, sin bx) dx: ∫ eˣ/(1 + cos x) dx.
"""
rehyp2f1(k::Real, σ::Real, ρ::Real, φ::Real) = real(_₂F₁(k, σ * im, 1 + σ * im, ρ * cis(φ)))
"""
    imhyp2f1(k, σ, ρ, φ)

Im ₂F₁(k, iσ; 1 + iσ; ρ e^{iφ}); see [`rehyp2f1`](@ref).
"""
imhyp2f1(k::Real, σ::Real, ρ::Real, φ::Real) = imag(_₂F₁(k, σ * im, 1 + σ * im, ρ * cis(φ)))
OPS[:rehyp2f1] = rehyp2f1
OPS[:imhyp2f1] = imhyp2f1

function try_exp_trig_hyp(f, x; build = nothing, lift = nothing, verify::Bool = true)
    @nospecialize f x
    xk = string(x)
    bd = Builder(build === nothing ? auto_build(f, x) : build, lift === nothing ? auto_lift(f, x) : lift, x)
    # f = (constants) · e^(a x + d) · g
    as, cs, gs = Any[], Any[], Any[]
    for (t, e) in product_factors!(Any[], f, 1)
        isexp = isnode(t) && ((opname(operation(t)) === :exp && length(arguments(t)) == 1) ||
                              (opname(operation(t)) === :^ && is_e_const(arguments(t)[1])))
        if isexp && depends_on(t, xk)
            u = arguments(t)[end]
            pp = poly_parts(bd, u, xk)
            (pp === nothing || maximum(keys(pp)) != 1) && return nothing
            push!(as, e == 1 ? pp[1] : mk(bd, :*, bd.lift(e), pp[1]))
            haskey(pp, 0) && push!(cs, mk(bd, :exp, e == 1 ? pp[0] : mk(bd, :*, bd.lift(e), pp[0])))
        elseif !depends_on(t, xk)
            push!(cs, e == 1 ? t : mk(bd, :^, t, bd.lift(e)))
        else
            push!(gs, e == 1 ? t : mk(bd, :^, t, bd.lift(e)))
        end
    end
    (isempty(as) || isempty(gs)) && return nothing
    a = length(as) == 1 ? as[1] : mk(bd, :+, as...)
    g = length(gs) == 1 ? gs[1] : mk(bd, :*, gs...)
    T, el = try
        build_tower(g, xk)
    catch e
        (e isa RischNotImplemented || e isa RischError || e isa NeedComplex) && return nothing
        rethrow()
    end
    (ctype(T) === QI && length(T.levels) == 1 && T.levels[1].kind === :exp && levelof(T, el) == 1) || return nothing
    U = T.levels[1].arg
    (isone(U.den) && degree(U.num) == 1 && iszero(U.num.c[1])) || return nothing
    b = to_real(U.num.c[2] * inv(cimag(QI)))
    b isa Q || return nothing                               # E = e^(ibx)
    cst(c) = const_value(T, c)
    Nc, Dc = [cst(c) for c in el.num.c], [cst(c) for c in el.den.c]
    (any(isnothing, Nc) || any(isnothing, Dc)) && return nothing
    P = UPoly{QI}
    N, D = P(QI[Nc...]), P(QI[Dc...])
    l = lc(D)
    N, D = scale(inv(l), N), scale(inv(l), D)
    Qp, Rm = divrem(N, D)
    # the roots of D (all in ℚ(i)) with multiplicities
    roots = Tuple{QI,Int}[]
    rest = D
    for r in constant_roots(quo(D, gcd(D, deriv(D))))       # (on the squarefree part)
        lin = P(QI[-r, one(QI)])
        μ = 0
        while degree(rest) > 0 && iszero(rem(rest, lin))
            rest = quo(rest, lin)
            μ += 1
        end
        push!(roots, (r, μ))
    end
    degree(rest) == 0 || return nothing
    # c_{r,k}: the Laurent coefficients of Rm/D at r, from h(r + t) = Rm/(D/(E - r)^μ) as a series in t
    shift(p, r) = foldr((c, acc) -> acc * P(QI[r, one(QI)]) + P(QI[c]), p.c; init = zero(P))
    coef(p, k) = k + 1 <= length(p.c) ? p.c[k + 1] : zero(QI)
    terms = Tuple{QI,Int,QI}[]                              # (r, k, c): c/(E - r)ᵏ
    for (r, μ) in roots
        A, B = shift(Rm, r), shift(quo(D, P(QI[-r, one(QI)])^μ), r)
        s = QI[]                                             # A/B = Σ sⱼ tʲ
        for j in 0:(μ - 1)
            acc = coef(A, j)
            for i in 0:(j - 1)
                acc = acc - s[i + 1] * coef(B, j - i)
            end
            push!(s, acc / coef(B, 0))
        end
        for j in 0:(μ - 1)
            iszero(s[j + 1]) || push!(terms, (r, μ - j, s[j + 1]))
        end
    end
    # exact check of the decomposition
    F = Frac{P}
    tot = frac(Qp)
    for (r, k, c) in terms
        tot = tot + frac(P(QI[c]), P(QI[-r, one(QI)])^k)
    end
    tot == frac(N, D) || throw(RischError("internal check failed: partial fractions in step EH"))
    any(((r, _, _),) -> !iszero(r), terms) || return nothing  # (Laurent polynomial: elementary, the usual route)
    # output
    aq = leaf_rational(a)                                   # a rational: printed as such
    aq === nothing || (a = cterm(bd, Q(aq)))
    ea = mk(bd, :exp, aq === nothing ? mk(bd, :*, a, bd.x) : isone(aq) ? bd.x : mk(bd, :*, a, bd.x))
    diva(t) = (aq !== nothing && isone(aq)) ? t : mk(bd, :/, t, a)
    bx(n) = isone(n * b) ? bd.x : mk(bd, :*, cterm(bd, n * b), bd.x)
    qt(q::Q) = cterm(bd, q)
    out = Any[]
    lterm(n, p::QI) = begin                                 # Re[p e^(ax) Eⁿ/(a + ibn)]
        iszero(n) && return mk(bd, :*, qt(p.re), diva(ea))
        cn, sn = mk(bd, :cos, bx(n)), mk(bd, :sin, bx(n))
        lin(α, u, β, v) = iszero(α) ? mk(bd, :*, qt(β), v) : iszero(β) ? mk(bd, :*, qt(α), u) :
                          mk(bd, :+, mk(bd, :*, qt(α), u), mk(bd, :*, qt(β), v))
        A1 = lin(p.re, cn, -p.im, sn)                       # Re(p Eⁿ)
        B1 = lin(p.re, sn, p.im, cn)                        # Im(p Eⁿ)
        numt = mk(bd, :+, mk(bd, :*, A1, a), mk(bd, :*, qt(n * b), B1))
        dent = mk(bd, :+, mk(bd, :^, a, bd.lift(2)), qt((n * b)^2))
        mk(bd, :*, ea, mk(bd, :/, numt, dent))
    end
    for (i, p) in enumerate(Qp.c)
        iszero(p) || push!(out, lterm(i - 1, p))
    end
    σ = aq === nothing ? mk(bd, :*, qt(-1 / b), a) : qt(-Q(aq) / b)
    for (r, k, c) in terms
        if iszero(r)                                        # c E^(-k)
            push!(out, lterm(-k, c))
            continue
        end
        C = c * (QI(Q(-1), Q(0)) / r)^k                     # c/(E - r)ᵏ = C/(1 - E/r)ᵏ
        n2 = r.re^2 + r.im^2
        m = rat_sqrt(n2)
        ρ = m === nothing ? mk(bd, :/, bd.lift(1), mk(bd, :sqrt, qt(n2))) : qt(1 / m)
        ψ = axis_arg(r)                                     # arg r (× π on the axes)
        argr = ψ !== nothing ? (isone(ψ) ? bd.lift(π) : mk(bd, :*, qt(ψ), bd.lift(π))) :
               r.re > 0 ? mk(bd, :atan, qt(r.im / r.re)) :
               mk(bd, :+, mk(bd, :atan, qt(r.im / r.re)), bd.lift(π))
        φ = (ψ !== nothing && iszero(ψ)) ? bx(1) : mk(bd, :+, bx(1), mk(bd, :*, bd.lift(-1), argr))
        H(fn) = mk(bd, fn, bd.lift(k), σ, ρ, φ)
        parts = Any[]
        iszero(C.re) || push!(parts, mk(bd, :*, qt(C.re), H(:rehyp2f1)))
        iszero(C.im) || push!(parts, mk(bd, :*, qt(-C.im), H(:imhyp2f1)))
        push!(out, mk(bd, :*, diva(ea), length(parts) == 1 ? parts[1] : mk(bd, :+, parts...)))
    end
    tot_t = length(out) == 1 ? out[1] : mk(bd, :+, out...)
    isempty(cs) ? tot_t : mk(bd, :*, cs..., tot_t)
end
