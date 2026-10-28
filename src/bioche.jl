# ---------------------------------------------------------------------------
# Step TS: simpler trigonometric forms by Bioche's rules
#
# f rational in sin u, cos u (u = k x): in the ℚ(i) tower f = R(θ), θ = e^{iu}, R with constant
# coefficients. If the form ω = R du is invariant under
#   u ↦ -u      (R(1/θ) = -R(θ)):   s = cos u,  du/ds = -1/sin u = -2iθ/(θ² - 1)
#   u ↦ π - u   (R(-1/θ) = -R(θ)):  s = sin u,  du/ds = 1/cos u = 2θ/(θ² + 1)
#   u ↦ π + u   (R(-θ) = R(θ)):     s = tan u,  θ² = (1 + is)/(1 - is), du/ds = 1/(1 + s²)
# then ω = g(s) ds with g ∈ ℚ(s) (a function invariant under θ ↦ 1/θ is a rational function of
# (θ + 1/θ)/2, via θʲ + θ⁻ʲ = 2Tⱼ; for sin, θ = iη reduces to the cos case). g(s(θ))·s′ = f is
# checked exactly in the tower and ∫ g ds exactly in ℚ(s) (`check_result`), so the answer G(s(x))
# is verified by the chain rule. The rational integral has atans of polynomials (R3), so G(cos u),
# G(sin u) are continuous; G(tan u) jumps where tan u = ±∞: each c·atan(p) with p of odd degree and
# lc sign σ jumps by -cσπ, corrected by J(u - atan(tan u)) = Jπ⌊(u + π/2)/π⌋, J = Σ cσ (no π).
# Returns a term, or nothing (not of this kind: the general route is used).
# ---------------------------------------------------------------------------
# polynomials over the constant field C = ℚ(i) or ℚ(i)(t₁, …) (step TE: generic in C)
# p(c/θ)·θ^deg p  and  p(cθ)
θinv_poly(p::UPoly{C}, c::C) where {C} = UPoly{C}(reverse(C[p.c[k] * field_pow(c, k - 1) for k in eachindex(p.c)]))
θscale_poly(p::UPoly{C}, c::C) where {C} = UPoly{C}(C[p.c[k] * field_pow(c, k - 1) for k in eachindex(p.c)])
function θinv(R::Frac{UPoly{C}}, c::C) where {C}       # R(c/θ)
    θ = xpoly(C)
    frac(θinv_poly(R.num, c) * θ^degree(R.den), θinv_poly(R.den, c) * θ^degree(R.num))
end
θscale(R::Frac{UPoly{C}}, c::C) where {C} = frac(θscale_poly(R.num, c), θscale_poly(R.den, c))

# θ^(-sh)·M = Σ aⱼ θʲ, symmetric (aⱼ = a₋ⱼ), as a polynomial in s = (θ + 1/θ)/2, or nothing
function sym_laurent_to_s(M::UPoly{C}, sh::Int) where {C}
    n = degree(M) - sh
    a(j) = 0 <= j + sh < length(M.c) ? M.c[j + sh + 1] : zero(C)
    all(k -> iszero(M.c[k]), 1:max(0, sh - n)) || return nothing    # lowest exponent ≥ -n
    all(j -> a(j) == a(-j), 1:n) || return nothing
    P = UPoly{C}
    Tm, Tc = one(P), xpoly(C)                            # T₀, T₁
    out = scale(a(0), one(P))
    for j in 1:n
        out = out + scale(2 * a(j), Tc)
        Tm, Tc = Tc, scale(cfromQ(C, Q(2)), xpoly(C)) * Tc - Tm
    end
    out
end
# h(θ) with h(1/θ) = h(θ) as a rational function of s = (θ + 1/θ)/2
function sym_to_s(h::Frac{UPoly{C}}) where {C}
    Dr = θinv_poly(h.den, one(C))
    P = sym_laurent_to_s(h.num * Dr, degree(h.den))
    Qd = sym_laurent_to_s(h.den * Dr, degree(h.den))
    (P === nothing || Qd === nothing) ? nothing : frac(P, Qd)
end
# R(θ) = R̃(θ²): g(s) = R̃((1 + is)/(1 - is))/(1 + s²)
function tan_to_s(R::Frac{UPoly{C}}) where {C}
    N, D = R.num, R.den
    par(p) = all(k -> iszero(p.c[k]) || iseven(k - 1), eachindex(p.c)) ? 0 :
             all(k -> iszero(p.c[k]) || isodd(k - 1), eachindex(p.c)) ? 1 : nothing
    pn, pd = par(N), par(D)
    (pn === nothing || pn != pd) && return nothing
    half(p) = [p.c[k] for k in (1 + pn):2:length(p.c)]   # coefficients of ζ^0, ζ^1, … in p/θ^pn
    nc, dc = half(N), half(D)
    n = max(length(nc), length(dc)) - 1
    I = cimag(C)
    P = UPoly{C}
    ap, am = P(C[one(C), I]), P(C[one(C), -I])
    hom(cs) = sum(scale(cs[k + 1], ap^k * am^(n - k)) for k in 0:(length(cs) - 1))
    frac(hom(nc), hom(dc) * P(C[one(C), zero(C), one(C)]))
end

# x-jump coefficient of an atan argument p(s) at s = ±∞ (Σ c σ for odd degree), as a real sign
function atan_infinity_sign(p::Frac, sg = c -> Int(real_sign(c)))
    d = degree(p.num) - degree(p.den)
    (d > 0 && isodd(d)) || return 0
    sg(lc(p.num) / lc(p.den))                           # nothing: undecided (a parameter, step SY)
end

function bioche(f, x; build = nothing, lift = nothing)
    @nospecialize f x
    xk = string(x)
    T, el = try
        build_tower(f, xk)
    catch e
        e isa RischNotImplemented && return nothing
        rethrow()
    end
    C = ctype(T)
    # C = ℚ(i), or ℚ(i)(t₁, …) with real generators e^a, log p (step TE)
    (C === QI || (C <: Frac && cbase(C) === QI && all(g -> g.kind in (:exp, :log, :sym, :symlog), T.consts))) || return nothing
    (length(T.levels) == 1 && T.levels[1].kind === :exp) || return nothing
    RC = real_ctype(C)
    I = cimag(C)
    a = T.levels[1].arg
    (isone(a.den) && degree(a.num) == 1 && iszero(a.num.c[1])) || return nothing
    kr = to_real(a.num.c[2] * inv(I))
    k = kr === nothing ? nothing : kr isa Q ? kr : crational(kr)
    k === nothing && return nothing                      # θ = e^{iu}, u = k x, k ∈ ℚ
    levelof(T, el) == 1 || return nothing
    cs(p) = (v = [const_value(T, c) for c in p.c]; any(isnothing, v) ? nothing : UPoly{C}(C[c for c in v]))
    N, Dn = cs(el.num), cs(el.den)
    (N === nothing || Dn === nothing) && return nothing
    R = frac(N, Dn)
    P = UPoly{C}
    two = cfromQ(C, Q(2))
    θp = xpoly(C)
    K1 = T.Ts[1]
    θel = frac(xpoly(K1))
    one1 = one(θel)
    li(c) = lconst(T, c, 1)
    if θinv(R, one(C)) == -R                             # s = cos u
        kind = :cos
        g = sym_to_s(R * frac(scale(-2 * I, θp), θp^2 - one(P)))
        sel = (θel + one1 / θel) * li(inv(two))
    elseif θinv(R, -one(C)) == -R                        # s = sin u
        kind = :sin
        g = sym_to_s(θscale(R * frac(scale(two, θp), θp^2 + one(P)), I))
        sel = (θel - one1 / θel) * li(inv(2 * I))
    elseif θscale(R, -one(C)) == R                       # s = tan u
        kind = :tan
        g = tan_to_s(R)
        sel = li(-I) * (θel * θel - one1) / (θel * θel + one1)
    elseif any(g -> g.kind === :sym, T.consts)           # step TW: s = tan(u/2), θ = (1 + is)/(1 - is),
        kind = :half                                     # du/ds = 2/(1 + s²) (over parameter fields, where
        g = half_to_s(R)                                 # the ℚ(i) route has no quadratic residues)
        sel = li(-I) * (θel - one1) / (θel + one1)
    else
        return nothing
    end
    g === nothing && return nothing
    g = g * kconst(inv(cfromQ(C, k)))                    # dx = du/k
    rn, rd = [to_real(c) for c in g.num.c], [to_real(c) for c in g.den.c]
    (any(isnothing, rn) || any(isnothing, rd)) && return nothing
    gq = frac(UPoly{RC}(RC[rn...]), UPoly{RC}(RC[rd...]))
    # the substitution, exactly: g(s(θ))·ds/dx = f
    gs(p) = foldr((c, acc) -> acc * sel + li(to_complex(C, c)), p.c; init = zero(sel))
    gs(gq.num) / gs(gq.den) * D(T, 1, sel) == liftto(T, el, 1) ||
        throw(RischError("internal check failed: Bioche substitution"))
    # real poles of f (poles of g in the range of s) → the general route (real forms with |w|²)
    sg(c) = csign(c, T.consts)
    rng = kind in (:tan, :half) ? (nothing, nothing) : (-1, 1)
    nreal = real_root_count(gq.den, rng..., sg)
    # (tan(u/2) with parameters: whether the sign conditions are decided (by the caller's oracle, step SO)
    # or not, the answer holds between the real poles of g, on (-π, π) when the parameters leave none,
    # e.g. |a| < 1 for 1/(1 + a cos u); the general route has no parameter forms to offer instead)
    (nreal == 0 || kind === :half) || return nothing
    res = integrate_rational(gq)
    # residues of degree > 2 (step TR): a RootSum in s = cos u or sin u (over ℚ, real and continuous
    # since g has no pole in [-1, 1]); for s = tan u see step TT below
    unres = res.unresolved
    # step TB: for s = tan u without RootSums, the general route (TC/TH) gives a linear term plus atans
    # of trigonometric ratios with nonvanishing denominators (no tan, no correction terms); use it when
    # it is elementary and needed no tan(u/2) form, else the tan form below
    if kind === :tan && isempty(unres)
        HALF_ANGLE_FORMS[] = 0
        r = try
            Tg, elg = build_tower(f, xk)
            bdg = Builder(build === nothing ? auto_build(f, x) : build, lift === nothing ? auto_lift(f, x) : lift, x, Tg.consts)
            integrate_built(Tg, elg, bdg, true)
        catch e
            (e isa RischNotImplemented || e isa NotElementary) || rethrow()
            nothing
        end
        (r === nothing || r isa IntegralWithRootSums || HALF_ANGLE_FORMS[] > 0) || return r
    end
    # each log argument has constant sign on the range: log(-w) where it is negative (at s = 0)
    w0s = [sg(peval(w, zero(RC))) for (c, w) in res.logs]
    any(isnothing, w0s) && return nothing
    logs = Tuple{RC,UPoly{RC}}[(c, w0 < 0 ? -w : w) for ((c, w), w0) in zip(res.logs, w0s)]
    # log((U + √dV)/(U - √dV)) with a negative ratio: the same as log((dV + √dU)/(dV - √dU))
    quads = Any[]
    for q in res.quads
        if q isa QuadLog
            u0, v0 = peval(q.U, Q(0)), peval(q.V, Q(0))
            neg = real_sign(QS{q.d}(u0, v0)) * real_sign(QS{q.d}(u0, -v0)) < 0
            q = neg ? QuadLog(q.β, q.d, q.d * q.V, q.U) : q
        end
        push!(quads, q)
    end
    res = RationalIntegral(res.rational, logs, res.atans, Any[], quads)
    bd = Builder(build === nothing ? auto_build(f, x) : build, lift === nothing ? auto_lift(f, x) : lift, x, T.consts)
    ut = isone(k) ? bd.x : mk(bd, :*, cterm(bd, k), bd.x)
    kind === :half && (ut = mk(bd, :*, cterm(bd, k / 2), bd.x))   # s = tan(ku/2): u/2 plays the role of u
    st = mk(bd, kind === :half ? :tan : kind, ut)
    bs = Builder(bd.build, bd.lift, st, T.consts)       # prints s as sin(kx), cos(kx), tan(kx)
    if !isempty(unres)
        rss = Any[]
        for (rest, R, Dd) in unres
            append!(rss, root_sums(rest, R, Dd, string(st); arg = st))
        end
        check_with_rootsums(res, rss, gq) ||
            throw(RischError("internal check failed: derivative of the result (with RootSums) differs from the integrand"))
        if kind !== :tan
            rss = RC === Q ? rss : Any[base_term_rootsum(bs, rs) for rs in rss]
            E = to_term(bs, res)
            if kind === :half                            # jumps of the atans at u = π (not of the step PQ terms)
                corr = tan_jump_terms(bd, bs, res, sg)
                corr === nothing && return nothing
                isempty(corr) || (E = mk(bd, :+, E, mk(bd, :*, length(corr) == 1 ? corr[1] : mk(bd, :+, corr...),
                                                       mk(bd, :+, ut, mk(bd, :*, bd.lift(-1), mk(bd, :atan, mk(bd, :tan, ut)))))))
            end
            return with_rootsums(bd, E, rss)
        end
        # step TT: W(α, tan u) = cos(u)^(-n) W̃(α), W̃ = Σ w_k sin^k(u) cos^(n-k)(u), bounded and nonzero on
        # the real line (W monic: W̃ = ±1 where cos u = 0). So Σ α log W = Σ α log W̃ - (Σα) n log cos u,
        # the first continuous (F(a), step RN), the second real: -(Σα)·n/2·log(cos²u) (Σα ∈ RC since
        # m has coefficients in RC); its log singularity cancels against the logs in tan u, and the
        # atan jumps are corrected below as for elementary answers
        sin_t, cos_t = mk(bd, :sin, ut), mk(bd, :cos, ut)
        pw(t, e) = e == 1 ? t : mk(bd, :^, t, bd.lift(e))
        trs = Any[]
        clc = zero(RC)
        for rs in rss
            n = length(rs.W) - 1
            cs = Any[]
            for j in 1:degree(rs.poly)
                ts = Any[]
                for kk in eachindex(rs.W)
                    c = j <= length(rs.W[kk].c) ? rs.W[kk].c[j] : zero(RC)
                    iszero(c) && continue
                    mono = Any[]
                    kk - 1 > 0 && push!(mono, pw(sin_t, kk - 1))
                    n - kk + 1 > 0 && push!(mono, pw(cos_t, n - kk + 1))
                    t = isempty(mono) ? cterm(bs, c) :
                        isone(c) ? (length(mono) == 1 ? mono[1] : mk(bd, :*, mono...)) : mk(bd, :*, cterm(bs, c), mono...)
                    push!(ts, t)
                end
                push!(cs, isempty(ts) ? nothing : length(ts) == 1 ? ts[1] : mk(bd, :+, ts...))
            end
            push!(trs, TermRootSum(rs.poly, cs, xk, RC === Q ? nothing : Any[cterm(bs, c) for c in rs.poly.c]))
            clc = clc + n * (-rs.poly.c[end - 1])          # (Σα)·n, m monic
        end
        parts = Any[to_term(bs, res)]
        corr = tan_jump_terms(bd, bs, res, sg)
        corr === nothing && return nothing
        isempty(corr) || push!(parts, mk(bd, :*, length(corr) == 1 ? corr[1] : mk(bd, :+, corr...),
                                         mk(bd, :+, ut, mk(bd, :*, bd.lift(-1), mk(bd, :atan, mk(bd, :tan, ut))))))
        iszero(clc) || push!(parts, mk(bd, :*, cterm(bs, -clc / cfromQ(RC, Q(2))), mk(bd, :log, mk(bd, :^, cos_t, bd.lift(2)))))
        return IntegralWithRootSums(length(parts) == 1 ? parts[1] : mk(bd, :+, parts...), trs, xk)
    end
    check_result(res, gq) || throw(RischError("internal check failed: derivative of the result differs from the integrand"))
    term = to_term(bs, res)
    kind in (:tan, :half) || return term
    corr = tan_jump_terms(bd, bs, res, sg)
    corr === nothing && return nothing
    isempty(corr) && return term
    cc = length(corr) == 1 ? corr[1] : mk(bd, :+, corr...)
    mk(bd, :+, term, mk(bd, :*, cc, mk(bd, :+, ut, mk(bd, :*, bd.lift(-1), mk(bd, :atan, mk(bd, :tan, ut))))))
end

# the jumps of G(tan u) where tan u = ±∞: coefficient terms J with correction J·(u - atan(tan u))
# (nothing when a sign is undecided: the caller then uses the general route)
function tan_jump_terms(bd::Builder, bs::Builder, res::RationalIntegral, sg = c -> Int(real_sign(c)))
    corr = Any[]
    J = nothing
    for (c, p) in res.atans
        σ = atan_infinity_sign(p, sg)
        σ === nothing && return nothing
        J = J === nothing ? σ * c : J + σ * c
    end
    (J === nothing || iszero(J)) || push!(corr, cterm(bs, J))
    for q in res.quads
        if q isa QuadAtan
            σ = atan_infinity_sign(q.u)
            σ == 0 || push!(corr, mk(bd, :*, cterm(bd, q.c * σ), mk(bd, :sqrt, bd.lift(q.e))))
        elseif q isa RationalIntegral
            Jd = sum((c * atan_infinity_sign(p) for (c, p) in q.atans); init = zero(typeof(q.rational.num.c[1])))
            iszero(Jd) || push!(corr, cterm(bd, Jd))
        elseif q isa BiquadTerm                         # α/s (atan((2x + r)/s) + atan((2x - r)/s)): 2α/s
            j = biquad_jump(bd, q)
            j === nothing || push!(corr, j)
        elseif q isa QuarticNested                      # c √w atan(√w u): jump c σ √w (√w > 0)
            for (c, w, u) in q.natans
                σ = atan_infinity_sign(frac(u))
                σ == 0 || push!(corr, mk(bd, :*, cterm(bd, c * σ), mk(bd, :sqrt, cterm(bd, w))))
            end
        end
    end
    corr
end

# step TW: R(θ) with θ = (1 + is)/(1 - is), times 2/(1 + s²), as an element of C(s)
function half_to_s(R::Frac{UPoly{C}}) where {C}
    I = cimag(C)
    P = UPoly{C}
    a, b = P(C[one(C), I]), P(C[one(C), -I])             # θ = a/b
    hom(p) = sum((scale(c, a^(k - 1) * b^(degree(p) - k + 1)) for (k, c) in enumerate(p.c) if !iszero(c)); init = zero(P))
    dn, dd = degree(R.num), degree(R.den)
    N, Dn = hom(R.num), hom(R.den)                      # R(θ) = N/Dn · b^(dd - dn)
    N, Dn = dd >= dn ? (N * b^(dd - dn), Dn) : (N, Dn * b^(dn - dd))
    frac(scale(cfromQ(C, Q(2)), N), Dn * P(C[one(C), zero(C), one(C)]))
end
