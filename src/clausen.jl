# ---------------------------------------------------------------------------
# Step CL: ∫ x·R(sin kx, cos kx) by parts, with Clausen's function Cl₂(φ) = Im Li₂(e^(iφ)) = Σ sin(nφ)/n²
# (∫ x tan x, ∫ x sin³x/cos³x). In the ℚ(i) tower, θ = e^(ikx), f = x R(θ) + S(θ); S is integrated as usual.
# G = ∫ R = v + Σ c log W(θ) (Risch). Each W is lc·Π (θ - r)^m with roots r = 0 or on the unit circle in ℚ(i)
# (±1, ±i), r = e^(iψ), φ = kx - ψ; then log(θ - r) = log(-r) + log(1 - θ/r) and, on 0 < φ < 2π,
#   log(1 - e^(iφ)) = log|2 sin(φ/2)| + i (φ - π)/2,   log(-r) = i arg(-r),   log θ = i k x,
# with log|2 sin(φ/2)| printed as ½ log(2 - 2 cos φ).
# G is printed in this real form (Re v + Σ Re(c ·)), which differentiates to R wherever it is smooth, and
#   ∫ log|2 sin(φ/2)| dx = -Cl₂(φ)/k,   ∫ (φ - π)/2 dx = (φ - π)²/(4k),
# so ∫ x R = x G - ∫ G holds wherever G is smooth (the same printed G on both sides).
# ---------------------------------------------------------------------------
"""
    clausen2(φ)

Clausen's function Cl₂(φ) = Im Li₂(e^{iφ}) = Σₙ sin(nφ)/n², with Cl₂′(φ) = -log|2 sin(φ/2)|. RischIntegrate
uses it in answers such as ∫ x tan x dx.
"""
clausen2(φ::Real) = imag(li2(cis(φ)))
OPS[:Cl2] = clausen2

function try_x_trig(f, x; build = nothing, lift = nothing, verify::Bool = true)
    @nospecialize f x
    xk = string(x)
    T, el = try
        build_tower(f, xk)
    catch e
        (e isa RischNotImplemented || e isa RischError) && return nothing
        rethrow()
    end
    C = ctype(T)
    (C === QI && length(T.levels) == 1 && T.levels[1].kind === :exp && levelof(T, el) == 1) || return nothing
    a = T.levels[1].arg
    (isone(a.den) && degree(a.num) == 1 && iszero(a.num.c[1])) || return nothing
    I = cimag(C)
    kr = to_real(a.num.c[2] * inv(I))
    kr isa Q || return nothing
    k = kr                                              # θ = e^(ikx)
    # el = x R + S: the θ-coefficients of the numerator of degree ≤ 1 in x, the denominator's constant
    K0 = T.Ts[1]
    cst(c) = const_value(T, c)
    Dc = [cst(c) for c in el.den.c]
    any(isnothing, Dc) && return nothing
    Rc, Sc = C[], C[]
    for c in el.num.c                                   # c ∈ K0 = ℚ(i)(x)
        (isone(c.den) || degree(c.den) == 0) || return nothing
        degree(c.num) <= 1 || return nothing
        d0 = c.den.c[1]
        push!(Sc, isempty(c.num.c) ? zero(C) : c.num.c[1] / d0)
        push!(Rc, length(c.num.c) >= 2 ? c.num.c[2] / d0 : zero(C))
    end
    all(iszero, Rc) && return nothing
    K1 = T.Ts[2]
    θ = frac(xpoly(K0))
    li(c) = lconst(T, c, 1)
    ev(cs) = foldr((c, acc) -> acc * θ + li(c), cs; init = zero(θ))
    Dθ = ev(Dc)
    Rel, Sel = ev(Rc) / Dθ, ev(Sc) / Dθ
    res = try
        integrate_el(T, 1, Rel)
    catch e
        (e isa NotElementary || e isa RischNotImplemented) && return nothing
        rethrow()
    end
    (isempty(res.atans) && isempty(res.quads)) || return nothing
    kinds = sigma_kinds(T)
    bd = Builder(build === nothing ? auto_build(f, x) : build, lift === nothing ? auto_lift(f, x) : lift, x, T.consts)
    half = inv(cfromQ(C, Q(2)))
    v = liftto(T, res.v, 1)
    vr = (v + tconj(T, kinds, v, 1)) * li(half)         # Re v
    # (Im v + Σ Im(c log W) is constant, as G' = R is real: Re G suffices)
    # Re G and ∫ Re G as lists of terms
    Gts, IGts = Any[], Any[]
    if !iszero(vr)
        push!(Gts, real_term(bd, T, kinds, vr, 1))
        r2 = try
            integrate_el(T, 1, vr)
        catch e
            (e isa NotElementary || e isa RischNotImplemented) && return nothing
            rethrow()
        end
        push!(IGts, to_term_real(bd, T, 1, r2, vr))
    end
    πt = bd.lift(π)
    kxt = isone(k) ? bd.x : mk(bd, :*, cterm(bd, k), bd.x)
    sc(c, t) = isone(c) ? t : mk(bd, :*, cterm(bd, c), t)
    lin = Q(0)                                          # coefficient of x in Re G (from args and log θ)
    quad = Q(0)                                         # of x² in ∫ Re G
    for (c, W0) in res.logs
        W0 = liftto(T, W0, 1)                           # an element of K₁: a polynomial in θ over K₀
        (W0 isa Frac && degree(W0.den) == 0) || return nothing
        W = W0.num
        dW = cst(W0.den.c[1])
        dW === nothing && return nothing
        Wc = [cst(w) for w in W.c]
        any(isnothing, Wc) && return nothing
        Wc = [w / dW for w in Wc]
        Wp = UPoly{C}(C[w for w in Wc])
        cr, ci = c.re, c.im
        # roots with multiplicity
        rest = Wp
        roots = Tuple{QI,Int}[]
        while degree(rest) > 0
            rs = constant_roots(rest)
            isempty(rs) && return nothing
            r = rs[1]
            m = 0
            lin1 = UPoly{C}(C[-r, one(C)])
            while degree(rest) > 0 && iszero(rem(rest, lin1))
                rest = quo(rest, lin1)
                m += 1
            end
            push!(roots, (r, m))
        end
        lcW = lc(Wp)
        # Re(c log lcW) = cr log|lcW| - ci arg(lcW) (a constant: x·it in ∫ and nothing in G' )
        argq = axis_arg(lcW)
        argq === nothing && return nothing
        n2 = lcW.re^2 + lcW.im^2
        if !isone(n2) && !iszero(cr)
            lt = mk(bd, :*, cterm(bd, cr / 2), mk(bd, :log, cterm(bd, n2)))   # cr·½ log|lcW|²
            push!(Gts, lt)
            push!(IGts, mk(bd, :*, lt, bd.x))
        end
        argπ = -ci * argq                               # Re(c log lcW) imaginary part: -ci·arg (× π)
        for (r, m) in roots
            if iszero(r)                                # log θ = i k x: Re(c i k x) = -ci k x
                lin += -ci * k * m
                continue
            end
            (r.re^2 + r.im^2 == 1) || return nothing    # (Clausen forms for roots on the unit circle)
            ψ = axis_arg(r)                             # in units of π, ψ ∈ [0, 2)
            ψ === nothing && return nothing
            ψ = ψ < 0 ? ψ + 2 : ψ
            amr = axis_arg(-r)                          # arg(-r) ∈ (-1, 1] (× π)
            φt = iszero(ψ) ? kxt : mk(bd, :+, kxt, mk(bd, :*, cterm(bd, -ψ), πt))
            # Re(c log(θ - r)) = cr log|2 sin(φ/2)| - ci (arg(-r) + (φ - π)/2)
            if !iszero(cr)
                # (2 sin(φ/2))² = 2 - 2 cos φ, cos φ = cos(kx - ψπ) = ±cos kx or ±sin kx
                cs = mk(bd, iseven(Int(2ψ)) ? :cos : :sin, kxt)
                ls = mk(bd, :log, mk(bd, :+, bd.lift(2), mk(bd, :*, bd.lift(ψ < 1 ? -2 : 2), cs)))
                push!(Gts, sc(cr * m / 2, ls))                                 # ½ log (2 - 2 cos φ)
                push!(IGts, sc(-cr * m / k, mk(bd, :Cl2, φt)))                 # ∫: -Cl₂(φ)/k
            end
            if !iszero(ci)
                # -ci m (arg(-r) + (φ - π)/2) with φ - π = k x - (ψ + 1)π
                pm = mk(bd, :+, kxt, mk(bd, :*, cterm(bd, -(ψ + 1)), πt))      # φ - π
                push!(Gts, sc(-ci * m, mk(bd, :+, mk(bd, :*, cterm(bd, amr), πt), mk(bd, :/, pm, bd.lift(2)))))
                push!(IGts, sc(-ci * m, mk(bd, :+, mk(bd, :*, cterm(bd, amr), πt, bd.x),
                                               mk(bd, :/, mk(bd, :^, pm, bd.lift(2)), cterm(bd, 4 * k)))))
            end
        end
        if !iszero(argπ)
            push!(Gts, mk(bd, :*, cterm(bd, argπ), πt))
            push!(IGts, mk(bd, :*, cterm(bd, argπ), πt, bd.x))
        end
    end
    if !iszero(lin)
        push!(Gts, sc(lin, bd.x))
        push!(IGts, sc(lin / 2, mk(bd, :^, bd.x, bd.lift(2))))
    end
    sumt(ts) = isempty(ts) ? bd.lift(0) : length(ts) == 1 ? ts[1] : mk(bd, :+, ts...)
    F = mk(bd, :+, mk(bd, :*, bd.x, sumt(Gts)), mk(bd, :*, bd.lift(-1), sumt(IGts)))
    if !all(iszero, Sc)
        St = real_term(bd, T, kinds, Sel, 1)
        FS = risch_integrate(St, x; build = build, lift = lift, verify = verify)
        FS isa IntegralWithRootSums && return nothing
        F = mk(bd, :+, F, FS)
    end
    F
end

# arg(z)/π for z on an axis of ℚ(i) (0, 1, 1/2, -1/2), else nothing
function axis_arg(z::QI)
    iszero(z.im) && return z.re > 0 ? Q(0) : Q(1)
    iszero(z.re) && return z.im > 0 ? Q(1, 2) : Q(-1, 2)
    nothing
end
