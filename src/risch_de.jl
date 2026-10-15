# ---------------------------------------------------------------------------
# Step 9a: the Risch DE  y' + f y = g  in K_m = k(t) with arbitrary denominators
# (Bronstein ch. 6), when the Laurent-shaped solver above does not apply.
#   1. normal denominator (6.1): h = gcd(e, ∂e)/gcd(p, ∂p) (e = normal part of den g,
#      p = gcd(normal part of den f, e)); y = q/h gives a q' + b q = c with a = d_n h,
#      b = d_n h f - d_n Dh, c = d_n h² g, whose denominators are special (else: no solution).
#      Valid for weakly normalised f; f = j u' (all callers) has no simple normal poles.
#   2. special denominator (6.2, exp only): ν_t(q) ≥ n_t, q = r t^(n_t), clear t-powers.
#   3. degree bound (6.3) for a r' + b r = c in k[t].
#   4. SPDE (6.4): r = α h + β with h' + b̄ h = c̄, deg h ≤ M.
#   5. h: deg b̄ > 0 → top-down (6.5, no cancellation); b̄ ∈ k* → decoupled (exp) or
#      triangular (log) RDEs in k; b̄ = 0 → integration in K_m without new logarithms.
# Cancellation cases (Bronstein 6.6) are recognised, not solved: if one cannot be excluded
# and no solution is found, RischNotImplemented is raised instead of "no solution".
# The candidate is always verified exactly.
# ---------------------------------------------------------------------------
tval(p::UPoly) = iszero(p) ? typemax(Int) ÷ 2 : findfirst(c -> !iszero(c), p.c) - 1
# t-valuation of an element whose denominator is a power of t
tval(f::Frac) = iszero(f) ? typemax(Int) ÷ 2 : tval(f.num) - degree(f.den)

# (normal, special) parts of a polynomial in t: special = t^v for exp, 1 for log and the base (x)
function split_factor(T::Tower, m::Int, p::UPoly)
    (m > 0 && T.levels[m].kind === :exp) || return p, one(p)
    v = tval(p)
    st = xpoly(T.Ts[m])^v
    quo(p, st), st
end

# the element f of K_m as a polynomial in t, or nothing
as_poly(f::Frac) = isone(f.den) ? f.num : nothing

# the derivation on polynomials in the generator of level m (m = 0: d/dx on C[x])
polyD(T::Tower, m::Int, p::UPoly) = m == 0 ? deriv(p) : Dp(T, m, p)
# the coefficient field of the polynomials of level m (C at the base)
coeff_type(T::Tower, m::Int) = m == 0 ? ctype(T) : T.Ts[m]

# R(z) = res_t(d, A - z dD) ∈ K[z]: its roots are the residues of A/d at the roots of d
residue_poly(::Type{K}, d::UPoly, A::UPoly, dD::UPoly) where {K} = residue_resultant(d, A, dD)

# the simple-pole part d1 of the normal denominator of f (level m), and A with f = A/d1 + (no pole at d1)
function simple_pole_part(T::Tower, m::Int, f)
    dn, _ = split_factor(T, m, f.den)
    degree(dn) <= 0 && return nothing
    g = gcd(dn, deriv(dn))
    dstar = quo(dn, g)
    d1 = monic(quo(dstar, gcd(dstar, g)))
    degree(d1) <= 0 && return nothing
    s, _, _ = gcdex(quo(f.den, d1), d1)
    d1, rem(s * f.num, d1)
end

# positive integer roots of R ∈ k[z] (k = coefficients of level m): through the ℚ-coordinates
function positive_integer_roots(T::Tower, m::Int, R::UPoly)
    iszero(R) && throw(RischError("zero residue polynomial"))
    vs = m == 0 ? cflat_all(ctype(T), R.c) : flat(T, m - 1, R.c)
    g = zero(UPoly{Q})
    for j in eachindex(vs[1])
        g = gcd(g, UPoly{Q}(Q[v[j] for v in vs]))
    end
    degree(g) > 0 || return Int[]
    ns = Int[]
    for r in rational_roots(g)
        (isone(denominator(r)) && r > 0) || continue
        r <= 1000 || throw(RischNotImplemented("weak normalisation with a residue $r > 1000"))
        push!(ns, Int(numerator(r)))
    end
    ns
end

# Bronstein 6.1, WeakNormalizer: q ∈ k[t] such that f - Dq/q has no simple normal pole with a
# positive integer residue (then the normal-denominator bound is valid)
function weak_normalizer(T::Tower, m::Int, f)
    P = typeof(f.den)
    sp = simple_pole_part(T, m, f)
    sp === nothing && return one(P)
    d1, a = sp
    dd1 = polyD(T, m, d1)
    R = residue_poly(coeff_type(T, m), d1, a, dd1)
    q = one(P)
    for n in positive_integer_roots(T, m, R)
        q = q * gcd(a - n * dd1, d1)^n
    end
    q
end

# z ∈ k* (k = K_km) with z'/z = h: (:yes, z), :no or :unknown. Candidates as in
# `cancellation_exponent` (without w'): z = Π θᵢ^nᵢ (exp generators) Π aᵢ^nᵢ (log arguments)
# Π qⱼ^eⱼ (normal factors of the denominators of h), integer exponents; z is verified.
function logderiv_solve(T::Tower, km::Int, h)
    km < 0 && return iszero(h) ? (:yes, one(h)) : :no     # constants: z' = 0
    K = T.Ts[km + 1]
    iszero(h) && return (:yes, one(K))
    logderiv_shape_ok(T, h) || return :no
    lift(e) = liftto(T, e, km)
    cands, bases = K[], K[]
    gen_is_log = Bool[]
    for (i, lv) in enumerate(T.levels[1:km])
        lv.kind === :atan && continue                   # atan' is no logarithmic derivative (TA)
        if lv.kind === :exp
            push!(cands, lift(D(T, i - 1, lv.arg)))
            push!(bases, lift(theta(T, i)))
        else
            push!(cands, lift(lv.dtheta.c[1]))
            push!(bases, lift(lv.arg))
        end
        push!(gen_is_log, lv.kind === :log)
    end
    ngen = length(cands)
    qs, exact = factor_candidates(T, Any[h, gen_logderivs(T, km)...])
    for (l, q) in qs
        push!(cands, lift(D(T, l, q) / q))
        push!(bases, lift(q))
    end
    coarse = !exact
    r = solve_relation(T, lift(h), cands)
    r === nothing && return coarse ? :unknown : :no
    if !all(x -> isone(denominator(x)), r)
        return (coarse || any(gen_is_log[i] && !isone(denominator(r[i])) for i in 1:ngen)) ? :unknown : :no
    end
    z = one(K)
    for (ρ, bs) in zip(r, bases)
        iszero(ρ) || (z = z * bs^Int(numerator(ρ)))
    end
    D(T, km, z) / z == lift(h) ? (:yes, z) : :unknown
end
logderiv_status(T::Tower, km::Int, h) = (r = logderiv_solve(T, km, h); r isa Tuple ? :yes : r)

# a necessary condition for h to be a logarithmic derivative in a tower: in its top generator θ_ℓ,
# the polynomial part has degree ≤ 0 (θ'/θ = w', δq/q = (deg q) w' + proper for exp; proper for
# log; lower levels have degree 0), and at an exp level there is no θ^(-v) part
function logderiv_shape_ok(T::Tower, h)
    l = levelof(T, h)
    l == 0 && return true
    q, _ = divrem(h.num, h.den)
    degree(q) <= 0 || return false
    !(T.levels[l].kind === :exp && tval(h.den) > 0)
end

# v ∈ K_m with D v = h, where the only new logarithm allowed is κ log(u) = κ t (t = θ_m = log u):
# v, nothing (no such v) or :unknown
function integrate_poly_t(T::Tower, m::Int, h)
    r = try
        integrate_el(T, m, h)
    catch e
        e isa NotElementary && return nothing
        e isa RischNotImplemented && return :unknown
        rethrow()
    end
    # atan / quadratic terms: residues outside C, not of the form κ t' (see `integrate_log_poly`)
    (isempty(r.atans) && isempty(r.quads)) || return nothing
    v = liftto(T, r.v, m)
    tgt = zero(T.Ts[m + 1])
    for (cj, wj) in r.logs
        w = liftto(T, wj, m)
        tgt = tgt + lconst(T, cj, m) * (D(T, m, w) / w)
    end
    iszero(tgt) && return v
    T.levels[m].kind in (:log, :atan) || return nothing
    θ = theta(T, m)
    κ = dconst_value(T, tgt / D(T, m, θ))
    κ === nothing && return nothing
    v + lconst(T, κ, m) * θ
end

# primitive cancellation (Bronstein 6.6): h' + b h = c in k[t] (t = log u) with b = z'/z, z ∈ k*:
# (z h)' = z c, so h = (∫ z c)/z, polynomial in t of degree ≤ M. Returns h, nothing or :unknown.
function prim_cancel(T::Tower, m::Int, z, c::UPoly, M::Int)
    zm = liftto(T, z, m)
    w = integrate_poly_t(T, m, zm * frac(c))
    w isa Symbol && return w
    w === nothing && return nothing
    hq = w / zm                                         # + κ/z for any constant κ: degree 0 in t
    (isone(hq.den) && degree(hq.num) <= M) || return nothing
    hq.num
end

# SPDE (Bronstein 6.4): a q' + b q = c, deg q ≤ n, a, b, c ∈ k[t]. Returns (b̄, c̄, M, α, β):
# q = α h + β with h' + b̄ h = c̄, deg h ≤ M; or nothing (no solution).
function spde(T::Tower, m::Int, a::UPoly, b::UPoly, c::UPoly, n::Int)
    P = typeof(a)
    if n < 0
        return iszero(c) ? (zero(P), zero(P), 0, zero(P), zero(P)) : nothing
    end
    if degree(a) == 0
        ia = inv(a.c[1])
        return (scale(ia, b), scale(ia, c), n, one(P), zero(P))
    end
    g = gcd(a, b)
    if degree(g) > 0
        cq, cr = divrem(c, g)
        iszero(cr) || return nothing
        a, b, c = quo(a, g), quo(b, g), cq
        degree(a) == 0 && return spde(T, m, a, b, c, n)
    end
    s, t, _ = gcdex(b, a)                       # s b + t a = 1
    r0 = s * c
    qd, r = divrem(r0, a)                        # b r + a z = c with deg r < deg a
    z = t * c + qd * b
    res = spde(T, m, a, b + polyD(T, m, a), z - polyD(T, m, r), n - degree(a))
    res === nothing && return nothing
    b̄, c̄, M, α, β = res
    (b̄, c̄, M, a * α, a * β + r)
end

function rde_general(T::Tower, m::Int, f, g)
    # 0. weak normalisation (step 9c): y = z/q, z' + (f - Dq/q) z = g q
    q0 = weak_normalizer(T, m, f)
    if !isone(q0)
        qF = frac(q0)
        z = rde_general(T, m, f - frac(polyD(T, m, q0)) / qF, g * qF)
        return z === nothing ? nothing : z / qF
    end
    lv = m == 0 ? nothing : T.levels[m]
    islog = m == 0 || lv.kind in (:log, :atan)          # the base behaves as t = x primitive over C
    k = coeff_type(T, m)
    P = UPoly{k}
    F = T.Ts[m + 1]
    t = xpoly(k)
    undecided = false
    # 1. normal denominator
    dn, _ = split_factor(T, m, f.den)
    en, _ = split_factor(T, m, g.den)
    p = gcd(dn, en)
    h = quo(gcd(en, deriv(en)), gcd(p, deriv(p)))
    hF, dnF = frac(h), frac(dn)
    aP = dn * h
    bF = dnF * hF * f - dnF * frac(polyD(T, m, h))
    cF = dnF * hF * hF * g
    nb_, _ = split_factor(T, m, bF.den)                 # denominators must be special
    degree(nb_) > 0 && throw(RischError("RDE: b has a normal denominator after the normal-denominator step"))
    nc_, _ = split_factor(T, m, cF.den)
    degree(nc_) > 0 && return nothing                   # Bronstein 6.1: then no solution exists
    # 2. special denominator
    nt = 0
    if islog
        bP, cP = bF.num, cF.num                         # denominators are 1
    else
        wp = liftto(T, D(T, m - 1, lv.arg), m)          # w' as an element of K_m
        nb, nc = tval(bF), tval(cF)
        lowq = nb < 0 ? nc - nb : min(nc, 0)
        if nb == 0
            b0 = bF.num.c[1 + degree(bF.den)]           # coefficient of t^0 (den = t^v)
            s0 = cancellation_exponent(T, m, b0 / aP.c[1], D(T, m - 1, lv.arg))
            s0 === :unknown && (undecided = true)
            s0 isa Int && (lowq = min(lowq, s0))
        end
        nt = min(0, lowq)
        tn = frac(t)^nt
        b1 = bF + lq(T, Q(nt), m) * wp * frac(aP)
        c1 = cF / tn
        N = max(0, -tval(b1), -tval(c1))
        tN = frac(t^N)
        aP = aP * t^N
        bP, cP = as_poly(b1 * tN), as_poly(c1 * tN)
        (bP === nothing || cP === nothing) && throw(RischError("RDE: special denominator not cleared"))
    end
    # 3. degree bound for a r' + b r = c
    n, und = rde_degree_bound(T, m, aP, bP, degree(cP))
    und && (undecided = true)
    # 4. SPDE, 5. solve h' + b̄ h = c̄
    y = nothing
    sp = spde(T, m, aP, bP, cP, n)
    if sp !== nothing
        b̄, c̄, M, α, β = sp
        hsol = poly_rde_reduced(T, m, b̄, c̄, M)
        if hsol isa Symbol                              # :unknown from a cancellation case
            undecided = true
        elseif hsol !== nothing
            q = α * hsol + β
            num_, den_ = q, h
            nt >= 0 ? (num_ = num_ * t^nt) : (den_ = den_ * t^(-nt))
            y = frac(num_, den_)
        end
    end
    y !== nothing && D(T, m, y) + f * y == g && return y
    undecided && cancellation_undecided()
    nothing
end

# Degree bound n for a r' + b r = c in k[t] (Bronstein 6.3), dc = deg c (step 3 of `rde_general`,
# shared with `prde`). Returns (n, undecided): undecided when a cancellation case could not be
# decided, in which case n may be too small.
function rde_degree_bound(T::Tower, m::Int, aP::UPoly, bP::UPoly, dc::Int)
    islog = m == 0 || T.levels[m].kind in (:log, :atan)
    k = coeff_type(T, m)
    undecided = false
    da, db = degree(aP), degree(bP)
    if islog
        if iszero(bP)                                   # a r' = c
            n = max(0, dc - da + 1)
        elseif db > da
            n = max(0, dc - db)
        elseif db < da - 1
            n = max(0, dc - da + 1)
        elseif db == da - 1                             # cancellation: -lc(b)/lc(a) = m t' + z'?
            n = max(0, dc - db)
            mm = limited_log_multiple(T, m, -lc(bP) / lc(aP))
            mm === :unknown && (undecided = true)
            mm isa Int && (n = max(n, mm))
        else                                            # db == da: -lc(b)/lc(a) = z'/z? (step 9b)
            n = max(0, dc - db)
            st = logderiv_solve(T, m - 1, -lc(bP) / lc(aP))
            if st === :unknown
                undecided = true
            elseif st isa Tuple                         # β = -[t^(da-1)](a z' + b z)/(z lc(a)) = m t' + w'?
                z = st[2]
                e = scale(D(T, m - 1, z), aP) + scale(z, bP)
                ec = da >= 1 && length(e.c) >= da ? e.c[da] : zero(k)
                mm = limited_log_multiple(T, m, -ec / (z * lc(aP)))
                mm === :unknown && (undecided = true)
                mm isa Int && (n = max(n, mm))
            end
        end
    else
        n = max(0, dc - max(da, db))
        if db == da
            s0 = cancellation_exponent(T, m, lc(bP) / lc(aP), D(T, m - 1, T.levels[m].arg))
            s0 === :unknown && (undecided = true)
            s0 isa Int && (n = max(n, s0))
        end
    end
    n, undecided
end

# h' + b h = c in k[t], deg h ≤ M; returns h, nothing (no solution) or :unknown
function poly_rde_reduced(T::Tower, m::Int, b::UPoly, c::UPoly, M::Int)
    P = typeof(b)
    k = coeff_type(T, m)
    zk = zero(k)
    iszero(c) && return zero(P)
    M < 0 && return nothing
    if m == 0 && iszero(b)                              # base: h' = c in C[x]
        h = integrate_poly(c)
        return degree(h) <= M ? h : nothing
    end
    lv = m == 0 ? nothing : T.levels[m]
    if degree(b) > 0 || m == 0                          # no cancellation (6.5); at the base also b ∈ C*
        h = zero(P)
        n = M
        while !iszero(c)
            mm = degree(c) - degree(b)
            (n < 0 || mm < 0 || mm > n) && return nothing
            cs = fill(zk, mm + 1)
            cs[mm + 1] = lc(c) / lc(b)
            pq = P(cs)
            h = h + pq
            n = mm - 1
            c = c - polyD(T, m, pq) - b * pq
        end
        return h
    end
    if iszero(b)                                        # h' = c: no new logarithms (log: κ t allowed)
        v = lv.kind in (:log, :atan) ? integrate_poly_t(T, m, frac(c)) : integrate_const(T, m, frac(c))
        v isa Symbol && return v
        (v === nothing || !isone(v.den) || degree(v.num) > M) && return nothing
        return v.num
    end
    b0 = b.c[1]                                         # b ∈ k*
    degree(c) > M && return nothing
    cs = fill(zk, M + 1)
    if lv.kind === :exp                                 # decoupled: h_i' + (b + i w') h_i = c_i
        wp = D(T, m - 1, lv.arg)
        for i in 0:M
            ci = i + 1 <= length(c.c) ? c.c[i + 1] : zk
            iszero(ci) && continue
            fi = b0 + i * wp
            hi = iszero(fi) ? integrate_const(T, m - 1, ci) : rde(T, m - 1, fi, ci)
            hi === nothing && return nothing
            cs[i + 1] = hi
        end
        return P(cs)
    end
    # log: b = z'/z → (z h)' = z c (step 9b); else triangular, h_i' + b h_i = c_i - (i+1) h_(i+1) t'
    st = logderiv_solve(T, m - 1, b0)
    st isa Tuple && return prim_cancel(T, m, st[2], c, M)
    tp = lv.dtheta.c[1]
    for i in M:-1:0
        ci = i + 1 <= length(c.c) ? c.c[i + 1] : zk
        rhs = i + 1 <= M ? ci - (i + 1) * cs[i + 2] * tp : ci
        hi = iszero(rhs) ? zk : rde(T, m - 1, b0, rhs)
        if hi === nothing
            return st === :no ? nothing : :unknown
        end
        cs[i + 1] = hi
    end
    P(cs)
end

# -lc(b)/lc(a) = m t' + z' with z ∈ k and m ∈ ℤ, t = log u (limited integration, Bronstein 7.2)?
# Returns the integer m, nothing (no such m) or :unknown.
function limited_log_multiple(T::Tower, m::Int, α)
    if m == 0                                           # α ∈ C, t = x: α = m·1 + w' with w' = 0
        mi = cinteger(α)
        return mi === nothing ? nothing : Int(numerator(mi))
    end
    r = try
        integrate_el(T, m - 1, α)
    catch e
        e isa NotElementary && return nothing
        e isa RischNotImplemented && return :unknown
        rethrow()
    end
    # SpecialTerm: ∫α is not elementary at all; atan / quadratic terms: residues outside C
    (isempty(r.atans) && isempty(r.quads)) || return nothing
    K = T.Ts[m]
    tgt = zero(K)
    for (cj, wj) in r.logs
        tgt = tgt + lconst(T, cj, m - 1) * (D(T, m - 1, wj) / wj)
    end
    iszero(tgt) && return 0
    cv = dconst_value(T, tgt / T.levels[m].dtheta.c[1])
    cv === nothing && return nothing
    mi = cinteger(cv)
    mi === nothing ? nothing : Int(numerator(mi))
end

cancellation_undecided() = throw(RischNotImplemented(
    "Risch DE, cancellation case: whether f₀ + s·w' is a logarithmic derivative in k could not be decided"))

# Step 8b. The integers s for which  c' + (f₀ + s w') c = 0  has a solution c ∈ k* (k = K_(m-1),
# t = θ_m = exp(w)): then -(f₀ + s w') = c'/c is a logarithmic derivative in k. Writing
# c = (constant) Π θᵢ^(nᵢ) Π qⱼ^(eⱼ) (generators of k and normal irreducible factors, all
# exponents integers), c'/c = Σ nᵢ bᵢ' + Σ eⱼ δqⱼ/qⱼ with bᵢ' the derivative of an exp argument
# or θᵢ' = aᵢ'/aᵢ of a log; the qⱼ show up in the denominators of f₀ and w'. So solve
#     f₀ = Σ ρᵢ (candidates) - s w'     over ℚ.
# w' is not in the span of logarithmic derivatives (t is a monomial over k), so s is unique:
# a non-integer s means no cancellation. The factor list (squarefree factors, split by rational
# roots at the base) can be too coarse; in that case the answer is :unknown, never a guess.
# Returns an Int, `nothing` (no cancellation) or :unknown.
function cancellation_exponent(T::Tower, m::Int, f0, wp)
    km = m - 1
    # s w' cannot change the top-level shape of f0 when f0 lies higher than w'
    (levelof(T, f0) > levelof(T, wp) && !logderiv_shape_ok(T, f0)) && return nothing
    K = T.Ts[m]                                         # the type of k = K_km
    lift(e) = liftto(T, e, km)
    cands = K[]
    gen_is_log = Bool[]
    for (i, lv) in enumerate(T.levels[1:km])
        lv.kind === :atan && continue                   # atan' is no logarithmic derivative (TA)
        push!(cands, lift(lv.kind === :exp ? D(T, i - 1, lv.arg) : lv.dtheta.c[1]))
        push!(gen_is_log, lv.kind === :log)
    end
    ngen = length(cands)
    # factors of f0, w' and of the generators' own log-derivatives (e.g. a'/a of a log), refined
    qs, exact = factor_candidates(T, Any[f0, wp, gen_logderivs(T, km)...])
    for (l, q) in qs
        push!(cands, lift(D(T, l, q) / q))
    end
    coarse = !exact
    r = solve_relation(T, lift(f0), K[cands; lift(wp)])
    r === nothing && return coarse ? :unknown : nothing
    s = -r[end]
    isone(denominator(s)) || return nothing             # unique s, not an integer
    ρ = r[1:(end - 1)]
    if !all(x -> isone(denominator(x)), ρ)
        # a non-integer exponent of an exp generator means c ∉ k; of a log argument or a factor,
        # c could still be in k (a perfect power), so do not decide
        (coarse || any(gen_is_log[i] && !isone(denominator(ρ[i])) for i in 1:ngen)) && return :unknown
        return nothing
    end
    Int(numerator(s))
end

# Normal factors (level, q) of the denominators in h (level l), at every level. At h's own top
# level the simple-pole factors are split by residue (Rothstein–Trager): q_c = gcd(d1, A - c·Dd1)
# collects the irreducible factors where h has residue c. Lower levels (coefficients of h) are
# split by rational roots at the base only. Returns `exact`: every group either has a uniform
# residue in h or is linear (irreducible); otherwise a log-derivative test using these factors
# may be incomplete, and callers answer :unknown instead of "no".
function normal_factors!(out, T::Tower, h, l::Int; top::Bool = true)
    iszero(h) && return true
    exact = true
    d, _ = split_factor(T, l, h.den)
    if degree(d) > 0
        for (p, k) in squarefree(d)
            p = monic(p)
            exact &= (top && k == 1) ? residue_split!(out, T, l, h, p) : linear_split!(out, T, l, p)
        end
    end
    if l > 0
        for c in h.num.c
            exact &= normal_factors!(out, T, c, l - 1; top = false)
        end
        for c in h.den.c
            exact &= normal_factors!(out, T, c, l - 1; top = false)
        end
    end
    exact
end

# rational-root split at the base (linear factors are irreducible); elsewhere only degree 1 is exact
function linear_split!(out, T::Tower, l::Int, p::UPoly)
    if l > 0
        push!(out, (l, frac(p)))
        return degree(p) == 1
    end
    rest = p
    CC = eltype(p.c)
    for r in constant_roots(rest)
        lin = UPoly{CC}(CC[-r, one(CC)])
        push!(out, (0, frac(lin)))
        rest = quo(rest, lin)
    end
    degree(rest) > 0 || return true
    push!(out, (0, frac(monic(rest))))
    degree(rest) == 1
end

# split the simple factor p of h's denominator (level l) by the residues of h
function residue_split!(out, T::Tower, l::Int, h, p::UPoly)
    s, _, _ = gcdex(quo(h.den, p), p)
    A = rem(s * h.num, p)
    dP = polyD(T, l, p)
    K = coeff_type(T, l)
    R = residue_poly(K, p, A, dP)
    if degree(R) <= 0
        push!(out, (l, frac(p)))
        return degree(p) == 1
    end
    Rm = monic(R)
    CT = ctype(T)
    cs = CT[]
    for c in Rm.c                                      # residues must be constants
        v = l == 0 ? c : dconst_value(T, c)
        if v === nothing
            push!(out, (l, frac(p)))
            return degree(p) == 1
        end
        push!(cs, v)
    end
    Rc = UPoly{CT}(cs)
    Rc = quo(Rc, gcd(Rc, deriv(Rc)))
    rest = p
    for c in constant_roots(Rc)
        cl = l == 0 ? c : lconst(T, c, l - 1)
        gc = gcd(rest, A - scale(cl, dP))
        degree(gc) > 0 || continue
        push!(out, (l, frac(monic(gc))))
        rest = quo(rest, gc)
    end
    degree(rest) > 0 || return true
    push!(out, (l, frac(monic(rest))))
    degree(rest) == 1
end

# the element as an element of the lowest level it lies in (inverse of `liftto`)
function unlift(T::Tower, h)
    l = levelof(T, h)
    while l > 0 && isone(h.den) && degree(h.num) <= 0
        h = isempty(h.num.c) ? zero(T.Ts[l]) : h.num.c[1]
        l -= 1
    end
    h
end

# the generators' logarithmic derivatives of K_km at their own levels (exp: b', log: a'/a)
gen_logderivs(T::Tower, km::Int) =
    Any[lv.kind === :exp ? D(T, i - 1, lv.arg) : lv.dtheta.c[1] for (i, lv) in enumerate(T.levels[1:km])]

# factors of the given elements (each at its own level), refined; and whether they are exact
function factor_candidates(T::Tower, elems)
    qs = Tuple{Int,Any}[]
    exact = true
    for e in elems
        u = unlift(T, e)
        exact &= normal_factors!(qs, T, u, levelof(T, u))
    end
    refine_factors(qs), exact
end

# common refinement of factor lists (same level): replace overlapping q, q' by gcd and cofactors
function refine_factors(qs)
    L = unique(qs)
    changed = true
    while changed
        changed = false
        for i in eachindex(L), j in (i + 1):length(L)
            (li, fi), (lj, fj) = L[i], L[j]
            li == lj || continue
            g = gcd(fi.num, fj.num)
            degree(g) > 0 || continue
            new = Tuple{Int,Any}[(li, frac(monic(g)))]
            a, b = quo(fi.num, g), quo(fj.num, g)
            degree(a) > 0 && push!(new, (li, frac(monic(a))))
            degree(b) > 0 && push!(new, (lj, frac(monic(b))))
            L = unique(vcat([L[x] for x in eachindex(L) if x != i && x != j], new))
            changed = true
            break
        end
    end
    L
end
