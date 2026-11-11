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
# R(c/θ) == σ R and R(cθ) == R, as cross products (no gcd: the gcds of `frac` over a constant field with seven
# parameters took minutes, sample 3:473)
function θinv_is(R::Frac{UPoly{C}}, c::C, σ::Int) where {C}
    θ = xpoly(C)
    θinv_poly(R.num, c) * θ^degree(R.den) * R.den == scale(cfromQ(C, Q(σ)), R.num * θinv_poly(R.den, c) * θ^degree(R.num))
end
θscale_is(R::Frac{UPoly{C}}, c::C) where {C} = θscale_poly(R.num, c) * R.den == R.num * θscale_poly(R.den, c)

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
    if θinv_is(R, one(C), -1)                            # s = cos u
        kind = :cos
        g = sym_to_s(R * frac(scale(-2 * I, θp), θp^2 - one(P)))
        sel = (θel + one1 / θel) * li(inv(two))
    elseif θinv_is(R, -one(C), -1)                       # s = sin u
        kind = :sin
        g = sym_to_s(θscale(R * frac(scale(two, θp), θp^2 + one(P)), I))
        sel = (θel - one1 / θel) * li(inv(2 * I))
    elseif θscale_is(R, -one(C))                         # s = tan u
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
    # (tan(u/2) with parameters: whether the sign conditions are decided (by the caller's oracle, step SO)
    # or not, the answer holds between the real poles of g, on (-π, π) when the parameters leave none,
    # e.g. |a| < 1 for 1/(1 + a cos u); the general route has no parameter forms to offer instead. So the
    # count is not needed there: its Sturm sequence over ℚ(a, b, cos c, sin c) took minutes, sample 1910)
    # step TP: for s = tan u, real poles of g are poles of f (cot u, csc u: s = 0); the answer on each interval
    # between them, with log w² /2 for a log argument w that has real roots (the general route took minutes with
    # parameters: cot⁶/(a + b tan²)³, sample 1:476)
    realpoles = false
    if kind !== :half
        nr = real_root_count(gq.den, rng..., sg)
        if nr != 0
            # (with parameters only: without them the general route is quick, and its cot forms shorter, cot⁴ x)
            (kind === :tan && any(c -> c.kind === :sym, T.consts)) || return nothing
            # (undecided with parameters, a + b s² for a b of unknown sign: the full route, step TQ2)
            nr === nothing && return bioche_tan_full(f, x, gq, k, T; build = build, lift = lift)
            realpoles = true
        end
    end
    res = try
        integrate_rational(gq)
    catch e
        # step TQ2: residues over the parameters (1/(a + b s²): ±1/(2√(-ab))), which `integrate_rational` does not
        # take; the full route has the parameter forms (atan(√(b/a) s)/√(ab))
        (e isa RischNotImplemented && kind === :tan && any(c -> c.kind === :sym, T.consts)) || rethrow()
        return bioche_tan_full(f, x, gq, k, T; build = build, lift = lift)
    end
    # residues of degree > 2 (step TR): a RootSum in s = cos u or sin u (over ℚ, real and continuous
    # since g has no pole in [-1, 1]); for s = tan u see step TT below
    unres = res.unresolved
    if realpoles && (!isempty(unres) || any(q -> !(q isa QuadAtan), res.quads))
        return any(c -> c.kind === :sym, T.consts) ? bioche_tan_full(f, x, gq, k, T; build = build, lift = lift) : nothing
    end
    # step TB: for s = tan u without RootSums, the general route (TC/TH) gives a linear term plus atans
    # of trigonometric ratios with nonvanishing denominators (no tan, no correction terms); use it when
    # it is elementary and needed no tan(u/2) form, else the tan form below
    # (not with three or more parameters: over ℚ(i)(a, b, c, d) the general route took minutes, (a + b tan)³(c + d tan)²,
    # where the tan form takes seconds)
    if kind === :tan && isempty(unres) && !realpoles && count(c -> c.kind === :sym, T.consts) < 3
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
    logs = Tuple{RC,UPoly{RC}}[]
    for (c, w) in res.logs
        if realpoles                                     # (step TP) a log argument with real roots: (c/2) log w²
            nw = real_root_count(w, nothing, nothing, sg)
            nw === nothing && return nothing
            if nw > 0
                push!(logs, (c / cfromQ(RC, Q(2)), w * w))
                continue
            end
        end
        w0 = sg(peval(w, zero(RC)))
        w0 === nothing && return nothing
        push!(logs, (c, w0 < 0 ? -w : w))
    end
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
        # s = tan(u/2) with parameters: the RootSum's real form (atan(s √((a - 1)/(a + 1))) for 1/(a + cos u)) jumps at
        # u = π, which the correction below (over res's own atans) does not see; the full route takes the jumps of
        # its answer's atans (Jeffrey and Rich, ACM TOMS 20 (1994): the spurious discontinuities of tan(u/2))
        # (quadratic RootSums only: of degree 4, cos⁴u/(a + b cos u + c cos²u), the full route over ℚ(a, b, c) took over an
        # hour to return a RootSum again)
        if kind === :half && any(c -> c.kind === :sym, T.consts) && all(rs -> degree(rs.poly) <= 2, rss)
            r = bioche_tan_full(f, x, gq, k, T; build = build, lift = lift, half = true)
            r === nothing || return r
        end
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

# step TQ2: ∫ g(s) ds (s = tan u, u = k x) by the full route in Expr (g's parameters as symbols), s = tan u put back,
# with the jump correction K (u - atan(tan u)), K = Σ c (σ₊ - σ₋)/2 over the terms c atan(p) (σ± the signs of p at
# s = ±∞, at the parameters' generic values, as step SY). Checked numerically; nothing when the answer has a RootSum
# or a special function, or an atan argument does not go to ±∞ at both ends.
function bioche_tan_full(f, x, gq, k, T; build = nothing, lift = nothing, half::Bool = false)
    @nospecialize f x
    xk = string(x)
    sk = "s_tan"
    bx = Builder(expr_build, identity, Symbol(sk), T.consts)
    pt(p) = isempty(p.c) ? 0 : mk(bx, :+, (iszero(c) ? 0 : mk(bx, :*, cterm(bx, c), mk(bx, :^, Symbol(sk), j - 1)) for (j, c) in enumerate(p.c))...)
    leaves = Dict{String,Any}()
    toexpr(t) = safe_iscall(t) && !isempty(arguments(t)) ?
        Expr(:call, opname(operation(t)), (toexpr(a) for a in arguments(t))...) :
        (t isa Symbol || t isa Number) ? t : (s = term_to_expr(t); s isa Symbol && (leaves[string(s)] = t); s)
    g = toexpr(mk(bx, :/, pt(gq.num), pt(gq.den)))
    G = try
        risch_integrate(g, Symbol(sk); build = expr_build, lift = identity)
    catch e
        (e isa RischNotImplemented || e isa NotElementary) || rethrow()
        return nothing
    end
    (G isa IntegralWithRootSums || has_special(G)) && return nothing
    # (s = tan(u/2) spans the real line on (-π, π): a log of the full route, log(s + c) without |·|, turns negative on
    # part of it (1/(a + b cos u)², b > a); those answers stay with the Bioche forms, which take log(-w) there)
    half && has_op(G, :log) && return nothing
    # the jump coefficient over the terms c·atan(p) of G (a sum of products), each p at s = ±10⁸ with the parameters
    # where every p is real: the generic values, else larger ones (an answer with √(a² - 1) holds for a > 1, and
    # a = 0.8 makes p complex: 1/(a + cos u) by s = tan(u/2), half)
    # (the parameters: the symbols of G other than s, as Expr leaves; `leaves` only holds the user's non-Symbol leaves)
    syms!(acc, t) = t isa Symbol ? (t in (Symbol(sk), :π, :pi, :ℯ, :im) || push!(acc, string(t)); acc) :
                    t isa Expr ? (foreach(a -> syms!(acc, a), t.head === :call ? t.args[2:end] : t.args); acc) : acc
    names = sort!(unique([syms!(String[], G); [string(l) for l in keys(leaves)]]))
    function evat(vals)
        function e(t, s0)
            if t isa Expr && t.head === :call
                return op_function(t)((e(a, s0) for a in t.args[2:end])...)
            end
            t === Symbol(sk) && return complex(s0)
            ip = findfirst(==(string(t)), names)          # (not `k`: the closure would assign bioche_tan_full's k)
            ip === nothing || return complex(vals[ip])
            t in (:π, :pi) && return complex(π)
            t === :ℯ && return complex(ℯ)
            t isa Number && return complex(float(t))
            throw(RischError("no value for $t"))
        end
    end
    ev = numeric_evaluator(sk, G)
    flat(t) = (t isa Expr && t.head === :call && t.args[1] === :+) ? Any[u for a in t.args[2:end] for u in flat(a)] : Any[t]
    terms = flat(G)
    J = Any[]
    for t in terms
        fs = (t isa Expr && t.head === :call && t.args[1] === :*) ? t.args[2:end] : Any[t]
        ia = findall(u -> u isa Expr && u.head === :call && u.args[1] === :atan, fs)
        if isempty(ia)
            has_op(t, :atan) && return nothing
            continue
        end
        length(ia) == 1 || return nothing
        p = fs[ia[1]].args[2]
        c = Any[fs[j] for j in eachindex(fs) if j != ia[1]]
        has_x(Expr(:call, :*, 1, c...), sk) && return nothing
        vp, vm = nothing, nothing
        for vals in ([0.5 + 0.3j for j in eachindex(names)], [2.0 + 1.7j for j in eachindex(names)], [5.0 + 3.1j for j in eachindex(names)])
            a, b = try
                e = evat(vals)
                e(p, 1e8), e(p, -1e8)
            catch
                continue
            end
            (abs(imag(a)) <= 1e-8 * abs(a) && abs(imag(b)) <= 1e-8 * abs(b)) || continue
            vp, vm = real(a), real(b)
            break
        end
        vp === nothing && return nothing
        (abs(vp) > 1e4 && abs(vm) > 1e4) || return nothing
        σ = (Int(sign(vp)) - Int(sign(vm))) // 2
        σ == 0 || push!(J, σ == 1 ? (isempty(c) ? 1 : Expr(:call, :*, c...)) : Expr(:call, :*, σ, c...))
    end
    bd = Builder(build === nothing ? auto_build(f, x) : build, lift === nothing ? auto_lift(f, x) : lift, x)
    kk = half ? k / 2 : k                                # s = tan(k u/2): u/2 in the role of u
    ut = isone(kk) ? bd.x : mk(bd, :*, cterm(bd, kk), bd.x)
    st = mk(bd, :tan, ut)
    function back(ex)
        ex === Symbol(sk) && return st
        ex isa Symbol && return haskey(leaves, string(ex)) ? leaves[string(ex)] : ex === :ℯ ? mk(bd, :exp, bd.lift(1)) :
                                ex in (:π, :pi) ? bd.lift(π) : ex
        ex isa Number && return ex isa Rational ? cterm(bd, Q(ex)) : bd.lift(ex)
        (ex isa Expr && ex.head === :call) || return ex
        bd.build(op_function(ex), (back(a) for a in ex.args[2:end])...)
    end
    H = back(G)
    if !isempty(J)
        K = back(length(J) == 1 ? J[1] : Expr(:call, :+, J...))
        H = mk(bd, :+, H, mk(bd, :*, K, mk(bd, :+, ut, mk(bd, :*, bd.lift(-1), mk(bd, :atan, st)))))
    end
    numeric_antiderivative(f, H, xk) || return nothing
    H
end
