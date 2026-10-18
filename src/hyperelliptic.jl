# ---------------------------------------------------------------------------
# SI2 phase 1: hyperelliptic curves y² = a(x), a ∈ ℚ[x] squarefree, deg a ≥ 3 (genus ≥ 1)
#
# Integrands rational in x and y = √a. An element is p + q y (p, q ∈ ℚ(x)); {1, y} is an
# integral basis at every finite place (a squarefree). ∫p is a rational integral; by the
# involution y ↦ -y, ∫(p + q y) is elementary iff ∫ q y is. With q y = B/(D y):
#  * Hermite reduction, d(C y/Vᵏ) = (C′aV - kCV′a + CVa′/2)/(V^{k+1} y): for V coprime to a it
#    lowers V^m to V^{m-1} (m ≥ 2); for V | a (ramified places, a = VW) the numerator is
#    V (C′VW + CVW′/2 + (1/2 - k)CV′W), which lowers V^m to V^{m-1} for every m ≥ 1.
#  * reduction at infinity, d(xᵏ y) = (k x^{k-1} a + xᵏ a′/2)/y: deg P ≤ deg a - 2.
# The remainder (P + R/D)/y (D squarefree, coprime to a) has only simple poles. If it has no
# residues it is 0 or not elementary (Liouville: ω = dv with v integral, v = R₁ + R₂ y, and
# deg(R₂′a + R₂a′/2) ≥ deg a - 1 > deg P). Residues need the log part (phase 2, SI2_PLAN.md).
# ---------------------------------------------------------------------------

# p + q y in F(y), y² = a, F = K(x) (K = ℚ, or ℚ(√d) for the log part)
struct HypEl{F}
    p::F
    q::F
end
Base.:(==)(f::HypEl, g::HypEl) = f.p == g.p && f.q == g.q
hyp_add(f::HypEl, g::HypEl) = HypEl(f.p + g.p, f.q + g.q)
hyp_neg(f::HypEl) = HypEl(-f.p, -f.q)
hyp_mul(a, f::HypEl, g::HypEl) = HypEl(f.p * g.p + a * f.q * g.q, f.p * g.q + f.q * g.p)
function hyp_inv(a, f::HypEl)
    n = f.p * f.p - a * f.q * f.q                       # norm; nonzero since a is not a square
    iszero(n) && throw(DivideError())
    HypEl(f.p / n, -f.q / n)
end
function hyp_pow(a, f::HypEl, k::Integer)
    k < 0 && return hyp_pow(a, hyp_inv(a, f), -k)
    r, b = HypEl(one(a), zero(a)), f
    while k > 0
        isodd(k) && (r = hyp_mul(a, r, b))
        k >>= 1
        k > 0 && (b = hyp_mul(a, b, b))
    end
    r
end
# yᵏ
hyp_ypow(a::QXF, k::Integer) = iseven(k) ? HypEl(a^(k ÷ 2), zero(QXF)) : HypEl(zero(QXF), a^((k - 1) ÷ 2))

# the term t as an element of ℚ(x)(y); radval(ue, e) = u^e as a power of y (or nothing)
function parse_hyp(t, xk::String, a::QXF, radval)
    if safe_iscall(t)
        args = arguments(t)
        if !isempty(args)
            rp = radical_parts(t)
            if rp !== nothing
                e, ut = rp
                ue = radicand_element(ut, xk)
                k = ue === nothing ? nothing : radval(ue, e)
                k === nothing && throw(RischNotImplemented("radical $t: not a power of √($a)"))
                return hyp_ypow(a, k)
            end
            n = opname(operation(t))
            v = HypEl{QXF}[parse_hyp(u, xk, a, radval) for u in args]
            n === :+ && return foldl(hyp_add, v)
            n === :- && return length(v) == 1 ? hyp_neg(v[1]) : hyp_add(v[1], hyp_neg(foldl(hyp_add, v[2:end])))
            n === :* && return foldl((f, g) -> hyp_mul(a, f, g), v)
            n === :/ && length(v) == 2 && return hyp_mul(a, v[1], hyp_inv(a, v[2]))
            n === :inv && length(v) == 1 && return hyp_inv(a, v[1])
            if n === :^ && length(v) == 2
                k = iszero(v[2].q) ? const_int(v[2].p) : nothing
                (k === nothing || abs(k) > 10_000) &&
                    throw(RischNotImplemented("only small integer powers are supported over √($a)"))
                return hyp_pow(a, v[1], k)
            end
            throw(RischNotImplemented("`$n` in an integrand over √($a): only rational functions of x and √a are supported"))
        end
    end
    string(t) == xk && return HypEl(frac(xpoly(Q)), zero(QXF))
    r = leaf_rational(t)
    r !== nothing && return HypEl(kconst(r), zero(QXF))
    throw(RischNotImplemented("symbol `$t` is not the integration variable"))
end

# C ≡ B / M mod V
function hyp_solve_mod(B::P, M::P, V::P) where {P<:UPoly}
    s, _, g = gcdex(rem(M, V), V)
    isone(g) || throw(RischError("hyperelliptic Hermite reduction: gcd(M, V) ≠ 1"))
    rem(s * B, V)
end

# ∫ B/(D y) dx = g y + ∫ (P + R/D)/y dx, D squarefree and coprime to a, deg P ≤ deg a - 2
function hyp_reduce(a::QX, B::QX, D::QX)
    g = zero(QXF)
    da = deriv(a)
    while true
        h = gcd(B, D)
        degree(h) > 0 && (B = quo(B, h); D = quo(D, h))
        step = nothing
        for (V0, m) in squarefree(D)
            Va = gcd(V0, a)
            Vc = quo(V0, Va)
            if degree(Va) > 0                           # ramified: V^m → V^{m-1}, k = m
                step = (Va, m, true)
                break
            elseif m >= 2 && degree(Vc) > 0            # V^m → V^{m-1}, k = m - 1
                step = (Vc, m, false)
                break
            end
        end
        step === nothing && break
        V, m, ram = step
        Ds = quo(D, V^m)
        dV = deriv(V)
        if ram
            W = quo(a, V)
            k = m
            Cc = hyp_solve_mod(B, scale(Q(1) // 2 - k, Ds * dV * W), V)
            # d(C y/Vᵏ) = (C′VW + CVW′/2 + (1/2 - k)CV′W)/(Vᵏ y)
            Nn = deriv(Cc) * V * W + scale(Q(1) // 2, Cc * V * deriv(W)) + scale(Q(1) // 2 - k, Cc * dV * W)
        else
            k = m - 1
            Cc = hyp_solve_mod(B, scale(Q(-k), Ds * dV * a), V)
            # d(C y/Vᵏ) = (C′aV - kCV′a + CVa′/2)/(V^{k+1} y)
            Nn = deriv(Cc) * a * V - scale(Q(k), Cc * dV * a) + scale(Q(1) // 2, Cc * V * da)
        end
        g = g + frac(Cc, V^k)
        r, z = divrem(B - Ds * Nn, V)
        iszero(z) || throw(RischError("hyperelliptic Hermite reduction: numerator not divisible"))
        B, D = r, Ds * V^(m - 1)
    end
    P, R = divrem(B, D)
    n = degree(a)
    while degree(P) >= n - 1                            # at infinity: d(xᵏ y)
        k = degree(P) - n + 1
        c = lc(P) / (lc(a) * (k + Q(n) // 2))
        xk = xpoly(Q)^k
        dk = (k == 0 ? zero(QX) : scale(Q(k), xpoly(Q)^(k - 1) * a)) + scale(Q(1) // 2, xk * da)
        P = P - scale(c, dk)
        g = g + frac(scale(c, xk))
    end
    g, P, R, D
end

# y and 1/y at infinity, deg a = 2m: y = √lc(a) x^m A(1/x)^(1/2), 1/y = x^(-m) A(1/x)^(-1/2)/√lc(a), with
# A(t) = t^(2m) a(1/t)/lc(a). The coefficients s₀ … s_N of S = A^α, from A S′ = α A′ S:
# k s_k = Σ_{j≥1} (α j - (k - j)) A_j s_{k-j}.
function hyp_sqrt_series(a::QX, N::Int, α::Q)
    n = degree(a)
    A = Q[a.c[n + 1 - j] / lc(a) for j in 0:n]
    s = zeros(Q, N + 1)
    s[1] = 1
    for k in 1:N
        t = Q(0)
        for j in 1:min(k, n)
            t += (α * j - (k - j)) * A[j + 1] * s[k - j + 1]
        end
        s[k + 1] = t / k
    end
    s
end

# √lc(a) times the residue of P/y dx at ∞₊ (up to sign; -res at ∞₋), deg a = 2m: the coefficient of
# x^(-1) in P x^(-m) S(1/x), i.e. Σ_{j ≥ m-1} p_j s_{j-m+1}
function hyp_res_inf(a::QX, P::QX)
    m = degree(a) ÷ 2
    degree(P) < m - 1 && return Q(0)
    s = hyp_sqrt_series(a, degree(P) - m + 1, Q(-1, 2))
    sum(P.c[j + 1] * s[j - m + 2] for j in (m - 1):degree(P))
end

# residues of (P + R/D)/y: none iff R = 0 and (deg a odd or none at ∞±)
function hyp_residue_free(a::QX, P::QX, R::QX)
    iszero(R) || return false
    isodd(degree(a)) || iszero(hyp_res_inf(a, P))
end

# the polynomial part d of √a (lc(a) = l², deg a = 2m): deg(a - d²) < m
function hyp_sqrt_part(a::QX, l::Q)
    m = degree(a) ÷ 2
    d = scale(l, xpoly(Q)^m)
    for k in (m - 1):-1:0
        e = a - d * d
        c = m + k + 1 <= length(e.c) ? e.c[m + k + 1] : Q(0)
        d = d + scale(c / (2 * l), xpoly(Q)^k)
    end
    d
end

qx_bits(p::QX) = maximum((max(ndigits(numerator(c); base = 2), ndigits(denominator(c); base = 2)) for c in p.c); init = 0)

# A unit u = p + q y (p² - a q² = c ∈ ℚ*, q ≠ 0) of ℚ[x, y], y² = a, deg a even, lc(a) a square:
# the polynomial Pell equation, by the continued fraction of √a in ℚ((1/x)). Every solution is a
# convergent pₖ/qₖ, and pₖ² - a qₖ² = ±Q_{k+1}; the first constant Q_{k+1} gives the unit of least
# degree. Its divisor is n(∞₋ - ∞₊) with n = deg p, the order of ∞₊ - ∞₋ in the Jacobian.
# Returns (p, q), with p, q primitive integer polynomials and lc(p) > 0; `:none` when there is no
# unit with deg p ≤ maxdeg (deg pₖ grows with k: a proof); `nothing` when the search stopped at
# `maxbits` coefficient size first.
function hyp_pell(a::QX; maxdeg::Int, maxbits::Int = 2000)
    l = rat_sqrt(lc(a))
    l === nothing && return nothing
    d = hyp_sqrt_part(a, l)
    Pk, Qk = zero(QX), one(QX)
    p1, p0 = one(QX), zero(QX)                          # p_{k-1}, p_{k-2}
    q1, q0 = zero(QX), one(QX)
    while true
        ak = quo(Pk + d, Qk)
        p1, p0 = ak * p1 + p0, p1
        q1, q0 = ak * q1 + q0, q1
        degree(p1) > maxdeg && return :none
        Pk = ak * Qk - Pk
        Qk, z = divrem(a - Pk * Pk, Qk)
        iszero(z) || throw(RischError("hyp_pell: continued fraction step not exact"))
        if degree(Qk) == 0
            c = p1 * p1 - a * q1 * q1
            degree(c) == 0 || throw(RischError("hyp_pell: convergent is not a unit"))
            cs = vcat(p1.c, q1.c)                       # u ↦ k u changes log u by a constant
            k = Q(lcm(denominator.(cs)...)) / Q(gcd(numerator.(cs)...))
            lc(p1) < 0 && (k = -k)                      # u > 0 for large x
            return scale(k, p1), scale(k, q1)
        end
        max(qx_bits(Qk), qx_bits(q1)) > maxbits && return nothing
    end
end

# d(log u) = Pu/y for u = (p + q y)/G (G ∈ ℚ[x]; p, q ∈ K[x]), when N = p² - a q² = c·G²: the rational
# part N′/(2N) - G′/G vanishes and Pu = (p (q′a + q a′/2) - p′q a)/N
function hyp_dlog(a::P, p::P, q::P) where {P<:UPoly}
    two = one(P) + one(P)
    frac(p * (deriv(q) * a * two + q * deriv(a)) - two * deriv(p) * q * a, two * (p * p - a * q * q))
end

# exact check of d(log u) = Pu/y, u = (p + q y)/G, in K(x)(y)
function hyp_check_dlog(a::P, p::P, q::P, G::P, Pu) where {P<:UPoly}
    A = frac(a)
    up, uq = frac(p, G), frac(q, G)
    two = frac(one(P) + one(P))
    du = HypEl(dx(up), dx(uq) + uq * frac(deriv(a)) / (two * A))
    hyp_mul(A, du, hyp_inv(A, HypEl(up, uq))) == HypEl(zero(A), Pu / A)
end

hyp_invmod(M::P, V::P) where {P<:UPoly} = hyp_solve_mod(one(P), M, V)

# ℤ/pℤ (p < 2³¹ prime): a field for UPoly, used to filter linear systems (a trivial kernel mod p
# implies a trivial kernel over ℚ or ℚ(√d): reduction mod a prime can only lower the rank) and for
# torsion orders. One type for every p (no recompilation per prime): the modulus is HYP_MOD[], set by
# `with_mod` around each computation.
const HYP_MOD = Ref(2147483647)
function with_mod(f, p::Int)
    old = HYP_MOD[]
    HYP_MOD[] = p
    try
        f()
    finally
        HYP_MOD[] = old
    end
end
struct ModP
    v::Int
end
modp(n::Integer) = ModP(Int(mod(n, HYP_MOD[])))
function modp(q::Q)                                    # nothing when p divides the denominator
    d = mod(denominator(q), HYP_MOD[])
    iszero(d) ? nothing : modp(numerator(q)) * inv(ModP(Int(d)))
end
Base.zero(::Type{ModP}) = ModP(0)
Base.one(::Type{ModP}) = ModP(1)
Base.zero(::ModP) = ModP(0)
Base.one(::ModP) = ModP(1)
Base.iszero(a::ModP) = a.v == 0
Base.isone(a::ModP) = a.v == 1
Base.:(==)(a::ModP, b::ModP) = a.v == b.v
Base.:+(a::ModP, b::ModP) = ModP(mod(a.v + b.v, HYP_MOD[]))
Base.:-(a::ModP, b::ModP) = ModP(mod(a.v - b.v, HYP_MOD[]))
Base.:-(a::ModP) = ModP(mod(-a.v, HYP_MOD[]))
Base.:*(a::ModP, b::ModP) = ModP(mod(a.v * b.v, HYP_MOD[]))
Base.:*(n::Integer, a::ModP) = modp(n) * a
Base.inv(a::ModP) = iszero(a) ? throw(DivideError()) : ModP(powermod(a.v, HYP_MOD[] - 2, HYP_MOD[]))
Base.:/(a::ModP, b::ModP) = a * inv(b)
modp_chi(a::ModP) = iszero(a) ? 0 : (powermod(a.v, (HYP_MOD[] - 1) ÷ 2, HYP_MOD[]) == 1 ? 1 : -1)
function modp_sqrt(a::ModP)                            # a square root, or nothing (small p: by search)
    p = HYP_MOD[]
    modp_chi(a) == -1 && return nothing
    if p % 4 == 3
        return ModP(powermod(a.v, (p + 1) ÷ 4, p))
    end
    for t in 0:(p - 1)
        mod(t * t - a.v, p) == 0 && return ModP(t)
    end
    nothing
end
modp_roots(f::UPoly{ModP}) = [ModP(t) for t in 0:(HYP_MOD[] - 1) if iszero(peval(f, ModP(t)))]

# A reduction K → ℤ/pℤ for K = ℚ or ℚ(√d): (p, the map on constants, which returns nothing on a
# vanishing denominator; valid inside with_mod(p)). For ℚ(√d): p ≡ 3 mod 4 with d a square mod p.
hyp_reduction(::Type{Q}) = (2147483647, c -> modp(c))
function hyp_reduction(::Type{QS{d}}) where {d}
    p = 2147483647                                      # 2³¹ - 1 ≡ 3 mod 4
    while true
        if is_probable_prime(big(p)) && mod(d, p) != 0
            r = powermod(mod(d, p), (p + 1) ÷ 4, p)
            mod(r * r - d, p) == 0 && break
        end
        p -= 4
    end
    r = powermod(mod(d, p), (p + 1) ÷ 4, p)
    function φ(c::QS{d})
        a, b = modp(c.a), modp(c.b)
        (a === nothing || b === nothing) ? nothing : a + b * ModP(r)
    end
    p, φ
end
# a polynomial mapped coefficientwise (nothing if a coefficient fails)
function hyp_map(φ, p::UPoly, ::Type{T}) where {T}
    c = T[]
    for a in p.c
        m = φ(a)
        m === nothing && return nothing
        push!(c, m)
    end
    UPoly{T}(c)
end
hyp_lift(::Type{K}, p::QX) where {K} = UPoly{K}(K[cfromQ(K, c) for c in p.c])   # ℚ[x] → K[x]

# The finite residues of (P + R/D)/y (D squarefree, coprime to a and R), grouped by their class in
# ℚ*/ℚ*²: Dict d => [(G, s, S₀)], with residues ±s√d (s ∈ ℚ, s > 0, d squarefree) at the places over the
# roots of G (the product of the irreducible factors of D in that class), and y ≡ S = √d·S₀,
# S₀ ≡ R/(s d D′) mod G at the places with residue +s√d (y ≡ -S at those with -s√d).
# Over the roots α of a factor F: res = R(α)/(D′(α) y(α)), so res² ≡ R²/(D′² a) mod F. `nothing` when
# this is not a constant mod F (residues of degree > 2).
function hyp_finite_residues(a::QX, R::QX, D::QX)
    dD = deriv(D)
    byr = Dict{Tuple{Int,Q},QX}()
    for F in factor_Q(D)
        h = rem(R * R * hyp_invmod(dD * dD * a, F), F)
        degree(h) == 0 || return nothing
        d, sv = hyp_sqrt_class(h.c[1])
        byr[(d, sv)] = get(byr, (d, sv), one(QX)) * F
    end
    out = Dict{Int,Vector{Tuple{QX,Q,QX}}}()
    for ((d, sv), G) in byr
        push!(get!(out, d, Tuple{QX,Q,QX}[]), (G, sv, rem(R * hyp_invmod(scale(sv * d, dD), G), G)))
    end
    out
end

# c = (s√d)², s > 0, d squarefree: (d, s)
function hyp_sqrt_class(c::Q)
    n, m = numerator(c), denominator(c)
    σ, d = sqfree_split(n * m)                          # c = σ² d/m²
    Int(d), Q(σ) / Q(m)
end

# Y ≡ S mod G with Y² ≡ a mod Gᵉ (Newton; 2Y is a unit mod G since a is coprime to G)
function hyp_sqrt_lift(a::P, S::P, G::P, e::Int) where {P<:UPoly}
    Y, k = S, 1
    while k < e
        k = min(2k, e)
        Gk = G^k
        Y = rem(Y - (Y * Y - a) * hyp_invmod(Y + Y, Gk), Gk)
    end
    Y
end

# The shape of the system for N·Δ: degree bounds dp, dq of p, q, the conditions at infinity
# [(branch sign, pole order)], and the orders eᵢ = 2N nᵢ at the places Pᵢ
function hyp_shape(na::Int, degs, ns, ninf::Int, N::Int)
    es = [2N * n for n in ns]
    M = sum((es[i] * degs[i] for i in eachindex(es)); init = 0)
    if isodd(na)
        return fld(M, 2), fld(M - na, 2), Tuple{Int,Int}[], es
    end
    m = na ÷ 2
    op, om = M ÷ 2 - N * ninf, M ÷ 2 + N * ninf
    omax = max(op, om)
    omax, omax - m, (ninf == 0 ? Tuple{Int,Int}[] : [(op < om ? 1 : -1, min(op, om))]), es
end

# v = p + q y with div(v) ≥ Σ 2N nᵢ P_{rᵢ} - o₊∞₊ - o₋∞₋ (o± = M/2 ∓ N n∞, M = Σ 2N nᵢ deg Gᵢ; for deg a
# odd the single place at infinity, pole order ≤ M). The divisor has degree 0, so the solutions form a
# space of dimension ≤ 1, and dimension 1 iff N·Δ is principal (Δ = Σ nᵢ(P_{rᵢ} - σP_{rᵢ}) +
# n∞(∞₊ - ∞₋)): then (p, q), with p² - a q² = c·Π Gᵢ^(2N nᵢ); else nothing.
# res = [(Gᵢ, nᵢ, Sᵢ)]; l = √lc(a) (used only when n∞ ≠ 0).
function hyp_divisor_unit(a::UPoly{K}, res, ninf::Int, l, N::Int; maxsize::Int = 1500) where {K}
    na = degree(a)
    dp, dq, conds, es = hyp_shape(na, [degree(G) for (G, _, _) in res], [n for (_, n, _) in res], ninf, N)
    (dp < 0 && dq < 0) && return nothing
    dp + dq + 2 > maxsize && return :toolarge
    sq = isempty(conds) ? Q[] : hyp_sqrt_series(hyp_down(a), max(dq, 0) + na ÷ 2 - conds[1][2] + 1, Q(1, 2))  # y
    s = K[cfromQ(K, c) for c in sq]
    # filter mod p first, then the exact system over K
    pr, φ = hyp_reduction(K)
    trivial = with_mod(pr) do
        sp = ModP[]
        for c in s
            m = φ(c)
            m === nothing && return false
            push!(sp, m)
        end
        ap, lp = hyp_map(φ, a, ModP), l === nothing ? nothing : φ(l)
        resp = [(hyp_map(φ, G, ModP), n, hyp_map(φ, S, ModP)) for (G, n, S) in res]
        (ap === nothing || (l !== nothing && lp === nothing) ||
         any(r -> r[1] === nothing || r[3] === nothing, resp)) && return false
        colsp = hyp_divisor_cols(ap, resp, es, conds, sp, lp, dp, dq)
        isempty(nullspace_cols(colsp, length(colsp)))
    end
    trivial && return nothing
    cols = hyp_divisor_cols(a, res, es, conds, s, l, dp, dq)
    ker = nullspace_cols(cols, length(cols))
    isempty(ker) && return nothing
    v = ker[1]
    np = max(dp + 1, 0)
    p, q = UPoly{K}(v[1:np]), UPoly{K}(v[(np + 1):end])
    Gn = prod((res[i][1]^es[i] for i in eachindex(res)); init = one(a))
    c, z = divrem(p * p - a * q * q, Gn)
    (iszero(z) && degree(c) == 0) || throw(RischError("hyp_divisor_unit: the norm is not c·ΠGᵢ^(2N nᵢ)"))
    # the dominant term of p + q y at x → +∞ (y > 0): positive, so log's argument is positive there
    dom = (iszero(q) || (!iszero(p) && 2 * degree(p) >= 2 * degree(q) + na)) ? p : q
    if K === Q                                          # primitive, integer coefficients
        cs = vcat(p.c, q.c)
        k = Q(lcm(denominator.(cs)...)) / Q(gcd(numerator.(cs)...))
        lc(dom) < 0 && (k = -k)
    else
        k = inv(lc(dom))
    end
    scale(k, p), scale(k, q)
end

# a ∈ K[x] with rational coefficients, back in ℚ[x]
hyp_down(a::QX) = a
hyp_down(a::UPoly{QS{d}}) where {d} = QX(Q[(iszero(c.b) ? c.a : throw(RischError("hyp_down: irrational"))) for c in a.c])

# the columns of the linear system of `hyp_divisor_unit` over the field of a's coefficients (ℚ or
# ℤ/p): one per coefficient of p (x⁰ … x^dp), then of q; the rows are the coefficients of
# p + q Yᵢ mod Gᵢ^eᵢ, then the conditions at infinity
function hyp_divisor_cols(a::UPoly{T}, res, es, conds, s, l, dp::Int, dq::Int) where {T}
    P = UPoly{T}
    na = degree(a)
    m = na ÷ 2
    x = xpoly(T)
    mods = [(res[i][1]^es[i], hyp_sqrt_lift(a, res[i][3], res[i][1], es[i])) for i in eachindex(res)]
    top = max(dp, dq + m)
    cols = Vector{T}[]
    for (isq, d) in ((false, dp), (true, dq))
        d < 0 && continue
        rs = P[isq ? rem(Y, Ge) : rem(one(P), Ge) for (Ge, Y) in mods]
        for j in 0:d
            col = T[]
            for (i, (Ge, _)) in enumerate(mods)
                j > 0 && (rs[i] = rem(x * rs[i], Ge))   # xʲ (Yᵢ) mod Gᵢ^eᵢ, one step at a time
                r = rs[i]
                append!(col, [k <= length(r.c) ? r.c[k] : zero(T) for k in 1:degree(Ge)])
            end
            for (σ, o) in conds                         # [xᵏ] (p + σ l q x^m S(1/x)) = 0, o < k ≤ top
                for k in (o + 1):top
                    if isq
                        i = j + m - k
                        push!(col, i >= 0 ? σ * (l * s[i + 1]) : zero(T))
                    else
                        push!(col, j == k ? one(T) : zero(T))
                    end
                end
            end
            push!(cols, col)
        end
    end
    cols
end

# genus of y² = a, a squarefree
hyp_genus(a::QX) = (degree(a) - 1) ÷ 2

# --- torsion orders by reduction mod p ------------------------------------------------
# Let Δ = Σ nᵢ(Pᵢ - σPᵢ) + n∞(∞₊ - ∞₋) be defined over a number field L. For a prime 𝔭 of L with
# residue field 𝔽_p, p ≥ 7 (so e(𝔭/p) ≤ 4 < p - 1 for the fields used here) and y² = a of good
# reduction at p, reduction is injective on the torsion of the Jacobian (Katz): if Δ is torsion of
# order N, then Δ̄ has order N in Jac(𝔽_p). Two primes with different orders prove that Δ has infinite
# order; equal orders N leave one exact test (N·Δ principal or not). The order mod p divides #J(𝔽_p):
# #J = #C(𝔽_p) for genus 1, (N₁² + N₂)/2 - p for genus 2 (Nₖ = #C(𝔽_{pᵏ})); otherwise the Weil bound.

# #C(𝔽_p) for y² = ā (inside with_mod(p))
function hyp_count1(ap::UPoly{ModP})
    p = HYP_MOD[]
    n = sum(1 + modp_chi(peval(ap, ModP(t))) for t in 0:(p - 1))
    n + (isodd(degree(ap)) ? 1 : 1 + modp_chi(lc(ap)))
end

# #C(𝔽_{p²}): 𝔽_{p²} = 𝔽_p(w), w² = ν a non-residue; χ(z) = z^((p²-1)/2)
function hyp_count2(ap::UPoly{ModP})
    p = HYP_MOD[]
    ν = first(t for t in 2:(p - 1) if modp_chi(ModP(t)) == -1)
    mul((a, b), (c, d)) = (mod(a * c + ν * b * d, p), mod(a * d + b * c, p))
    function pw(z, e)
        r = (1, 0)
        while e > 0
            isodd(e) && (r = mul(r, z))
            z = mul(z, z)
            e >>= 1
        end
        r
    end
    cs = [c.v for c in ap.c]
    n = 0
    for u in 0:(p - 1), v in 0:(p - 1)
        z = (u, v)
        acc = (0, 0)
        for c in reverse(cs)
            acc = mul(acc, z)
            acc = (mod(acc[1] + c, p), acc[2])
        end
        χ = acc == (0, 0) ? 0 : (pw(acc, (p * p - 1) ÷ 2) == (1, 0) ? 1 : -1)
        n += 1 + χ
    end
    n + (isodd(degree(ap)) ? 1 : 2)                     # lc ∈ 𝔽_p is a square in 𝔽_{p²}
end

# the least N among `cand` with N·Δ̄ principal over 𝔽_p (Δ̄ from pts = [(α, β, n)], points (α, β) ∈ 𝔽_p²);
# nothing if none, :toolarge past the size cap. sp: the series of y at ∞ mod p (if ninf ≠ 0).
function hyp_order_modp(ap::UPoly{ModP}, pts, ninf::Int, lp, sp, cand; maxsize::Int = 2500)
    na = degree(ap)
    x = xpoly(ModP)
    res = [(x - UPoly{ModP}([α]), n, UPoly{ModP}([β])) for (α, β, n) in pts]
    for N in cand
        dp, dq, conds, es = hyp_shape(na, [1 for _ in pts], [n for (_, _, n) in pts], ninf, N)
        (dp < 0 && dq < 0) && continue
        dp + dq + 2 > maxsize && return :toolarge
        cols = hyp_divisor_cols(ap, res, es, conds, sp, lp, dp, dq)
        isempty(nullspace_cols(cols, length(cols))) || return N
    end
    nothing
end

# The order of Δ if it is torsion: :infinite (proved), the common order N mod two primes, or nothing
# (no suitable primes, or too large). ptsfun(p) (inside with_mod(p)) gives (pts, lp) for the reduction
# of Δ at a prime of degree 1 over p (or nothing if p is unsuitable: not split, ramified, bad).
function hyp_torsion_order(a::QX, ninf::Int, ptsfun; nprimes::Int = 2, pmax::Int = 400)
    g = hyp_genus(a)
    orders = Int[]
    p = 5
    while length(orders) < nprimes
        p += 2
        p > pmax && return nothing
        is_probable_prime(big(p)) || continue
        r = with_mod(p) do
            ap = hyp_map(modp, a, ModP)
            (ap === nothing || degree(ap) != degree(a) || degree(gcd(ap, deriv(ap))) != 0) && return nothing
            pl = ptsfun(p)
            pl === nothing && return nothing
            pts, lp = pl
            nJ = g == 1 ? hyp_count1(ap) : g == 2 ? (hyp_count1(ap)^2 + hyp_count2(ap)) ÷ 2 - p : 0
            cand = nJ > 0 ? sort!(Int.(divisors(big(nJ)))) : collect(1:floor(Int, (sqrt(p) + 1)^(2g)))
            sp = ModP[]
            if ninf != 0
                for c in hyp_sqrt_series(a, 2 * maximum(cand) * abs(ninf) + 2, Q(1, 2))
                    m = modp(c)
                    m === nothing && return nothing
                    push!(sp, m)
                end
            end
            N = hyp_order_modp(ap, pts, ninf, lp, sp, cand)
            N === nothing && throw(RischError("hyp_torsion_order: no order mod $p (it must divide #J = $nJ)"))
            N
        end
        r === nothing && continue
        r === :toolarge && return nothing
        push!(orders, r)
        orders[end] == orders[1] || return :infinite
    end
    orders[1]
end

# ptsfun for a class d (K = ℚ or ℚ(√d)): rd = [(G, n, S₀)], y ≡ √d·S₀ at Pᵢ over the roots of G; at ∞
# l = linf·√d∞ (used when ninf ≠ 0, then d∞ = d or 1)
function hyp_class_pts(d::Int, rd, linf::Q, dinf::Int)
    function (p)
        (d != 1 && mod(d, p) == 0) && return nothing
        sd = d == 1 ? one(ModP) : modp_sqrt(modp(d))
        sd === nothing && return nothing
        pts = Tuple{ModP,ModP,Int}[]
        for (G, n, S0) in rd
            Gp, Sp = hyp_map(modp, G, ModP), hyp_map(modp, S0, ModP)
            (Gp === nothing || Sp === nothing || degree(Gp) != degree(G)) && return nothing
            rts = modp_roots(Gp)
            length(rts) == degree(G) || return nothing     # split, distinct roots
            for α in rts
                β = sd * peval(Sp, α)
                iszero(β) && return nothing
                push!(pts, (α, β, n))
            end
        end
        length(unique(first.(pts))) == length(pts) || return nothing
        lp = modp(linf)
        lp === nothing && return nothing
        dinf == 1 || (lp = lp * (dinf == d ? sd : modp_sqrt(modp(dinf))))
        pts, lp
    end
end

# Residues of degree 4 (decision only): D = F irreducible of degree 2 with r² ≡ h mod F not constant,
# no residue at ∞. The residues are ±r₁, ±r₂, rⱼ = √h(αⱼ); r₁/r₂ ∈ ℚ iff h² ≡ c mod F with c/N(h) a
# square. If r₁, r₂ are ℚ-independent, the integral is elementary iff Δ₁ = P₁ - σP₁ is torsion
# (Δ₂ is its conjugate), P₁ = (α₁, R(α₁)/(r₁D′(α₁))) over L = ℚ(α₁, r₁).
function hyp_quartic_decision(a::QX, R::QX, D::QX, ρ::Q, uterm)
    gen = hyp_genus(a)
    fs = factor_Q(D)
    (length(fs) == 1 && degree(D) == 2 && iszero(ρ)) || return RischNotImplemented(
        "√($uterm): residues of degree > 2 over ℚ: only one quadratic factor of the denominator, without " *
        "residues at ∞, is supported")
    F, dD = fs[1], deriv(D)
    h = rem(R * R * hyp_invmod(dD * dD * a, F), F)
    h2 = rem(h * h, F)
    if degree(h2) <= 0 && rat_sqrt((isempty(h2.c) ? Q(0) : h2.c[1]) / resultant(F, h)) !== nothing
        return RischNotImplemented("√($uterm): residues of degree 4 that are ℚ-dependent are not supported")
    end
    function ptsfun(p)
        Fp, Rp, hp, dp = (hyp_map(modp, f, ModP) for f in (F, R, h, dD))
        any(isnothing, (Fp, Rp, hp, dp)) && return nothing
        rts = modp_roots(Fp)
        length(rts) == 2 || return nothing              # F splits (so p ∤ disc F)
        any(α -> iszero(peval(hp, α)), rts) && return nothing
        α = rts[1]
        r = modp_sqrt(peval(hp, α))
        r === nothing && return nothing                 # a prime of degree 1 of L over p
        Tuple{ModP,ModP,Int}[(α, peval(Rp, α) / (r * peval(dp, α)), 1)], one(ModP)
    end
    ord = hyp_torsion_order(a, 0, ptsfun)
    ord === :infinite && return NotElementary(
        "√($uterm): the residues have degree 4 and are ℚ-independent, and the divisor P₁ - σP₁ has infinite " *
        "order in the Jacobian (its orders modulo two primes differ)")
    ord === nothing && return RischNotImplemented(
        "√($uterm): residues of degree 4: no suitable primes found to decide torsion")
    RischNotImplemented("√($uterm): residues of degree 4 whose divisor is probably torsion (order $ord mod two " *
                        "primes); constructing the logarithm over a quartic field is not implemented yet")
end

# The log part of (P + R/D)/y (simple poles, some residue ≠ 0): a list of (d, λ, p, q, G, λPu), one per
# class d of residues, with λ ∈ K = ℚ(√d) (ℚ for d = 1), p, q ∈ K[x], G ∈ ℚ[x], d(λ log((p + q y)/G)) =
# λPu/y and λPu ∈ ℚ(x); together they have the residues of the integrand. Or the exception to raise.
# * Residues only at ∞± (R = 0, lc(a) a square): the polynomial Pell equation.
# * Otherwise, by classes: residues ±s√d (finite places, and ∞± where the residue is -ρ/√lc(a)). In a
#   class, with b√d (b the gcd of the s), Δ_d = Σ (s/b)(P_s - σP_s) + n∞(∞₊ - ∞₋) over K, and the least
#   N with N·Δ_d principal gives λ = b√d/N. The √d are linearly independent over ℚ, so every class
#   must be torsion.
# Genus 1, N ≤ 12 / N ≤ 18 decides: Δ_d is a point of the Jacobian (an elliptic curve over ℚ) over ℚ
# (Mazur) or over ℚ(√d) (Kamienny–Kenku–Momose: torsion points over quadratic fields have order ≤ 18).
function hyp_log_part(a::QX, P::QX, R::QX, D::QX, uterm)
    gen = hyp_genus(a)
    na = degree(a)
    ρ = isodd(na) ? Q(0) : hyp_res_inf(a, P)            # √lc(a) · (−residue at ∞₊)
    l = isodd(na) ? nothing : rat_sqrt(lc(a))
    if iszero(R) && l !== nothing
        pq = hyp_pell(a; maxdeg = gen == 1 ? 12 : 60)
        pq === :none && gen == 1 && return NotElementary(
            "√($uterm): the residues are at ∞₊, ∞₋ only, and ∞₊ - ∞₋ has infinite order on the elliptic " *
            "curve (no unit p + q√a with deg p ≤ 12, Mazur's bound)")
        if !(pq isa Tuple)                              # genus ≥ 2: the order of ∞₊ - ∞₋ mod p
            ord = hyp_torsion_order(a, 1, p -> (lp = modp(l); lp === nothing ? nothing : (Tuple{ModP,ModP,Int}[], lp)))
            ord === :infinite && return NotElementary(
                "√($uterm): the residues are at ∞₊, ∞₋ only, and ∞₊ - ∞₋ has infinite order in the Jacobian " *
                "(its orders modulo two primes differ)")
            if ord isa Int                              # a unit of degree ord, if any
                pq = hyp_pell(a; maxdeg = ord, maxbits = typemax(Int))
                pq isa Tuple || return NotElementary(
                    "√($uterm): ∞₊ - ∞₋ is not torsion (its order mod p would be $ord, but there is no unit of degree $ord)")
            end
        end
        pq isa Tuple || return RischNotImplemented(
            "√($uterm): residues at infinity, but no unit p + q√a found (polynomial Pell equation " *
            "p² - a q² = c; search bound reached on a curve of genus $gen, no torsion order found)")
        pu, qu = pq
        Pu = hyp_dlog(a, pu, qu)
        λ = hyp_res_inf(a, P) / hyp_res_inf(a, Pu.num)
        return [(1, λ, pu, qu, one(QX), Pu * kconst(λ))]
    end
    fin = iszero(R) ? Dict{Int,Vector{Tuple{QX,Q,QX}}}() : hyp_finite_residues(a, R, D)
    fin === nothing && return hyp_quartic_decision(a, R, D, ρ, uterm)
    # ∞₊: residue -ρ/√lc(a) = s∞√d∞, lc(a) = σ² d∞/m²; l = √lc(a) ∈ ℚ(√d∞)
    dinf, linf = 1, Q(1)
    if !isodd(na)
        dinf, linf = hyp_sqrt_class(lc(a))
    end
    sinf = iszero(ρ) ? Q(0) : -ρ / (linf * dinf)        # -ρ/(linf √d∞) = (-ρ/(linf d∞)) √d∞
    classes = sort!(collect(union(keys(fin), iszero(sinf) ? Int[] : [dinf])))
    out = Any[]
    for d in classes
        K = d == 1 ? Q : QS{d}
        rd = get(fin, d, Tuple{QX,Q,QX}[])
        si = d == dinf ? sinf : Q(0)
        b = reduce(gcd, vcat([sv for (_, sv, _) in rd], iszero(si) ? Q[] : [abs(si)]))
        rtd = d == 1 ? one(K) : K(Q(0), Q(1))           # √d
        res = [(hyp_lift(K, G), Int(sv / b), scale(rtd, hyp_lift(K, S0))) for (G, sv, S0) in rd]
        ninf = Int(si / b)
        lK = isodd(na) ? nothing : (dinf == 1 ? cfromQ(K, linf) : d == dinf ? K(Q(0), linf) : nothing)
        (ninf != 0 && lK === nothing) && throw(RischError("hyp_log_part: ∞ residue in the wrong class"))
        aK = hyp_lift(K, a)
        cls = d == 1 ? "" : " (residues in ℚ√$d)"
        # the order by reduction mod p (any genus), else the search N ≤ Nmax (genus 1: a proof)
        ord = hyp_torsion_order(a, ninf, hyp_class_pts(d, [(G, res[i][2], S0) for (i, (G, _, S0)) in enumerate(rd)],
                                                       linf, dinf))
        ord === :infinite && return NotElementary(
            "√($uterm): the divisor of the residues$cls has infinite order in the Jacobian (its orders " *
            "modulo two primes differ)")
        Ns = ord isa Int ? [ord] : collect(1:(gen == 1 ? (d == 1 ? 12 : 18) : 12))
        found = false
        for N in Ns
            pq = hyp_divisor_unit(aK, res, ninf, lK, N)
            pq === nothing && continue
            pq === :toolarge && return RischNotImplemented(
                "√($uterm): the divisor of the residues is too large for the search (multiple N = $N)")
            pu, qu = pq
            G = prod((rd[i][1]^(N * res[i][2]) for i in eachindex(rd)); init = one(QX))
            λ = rtd * cfromQ(K, b / N)
            λPu = hyp_dlog(aK, pu, qu) * frac(UPoly{K}(K[λ]))
            push!(out, (d, λ, pu, qu, G, hyp_down_frac(λPu)))
            found = true
            break
        end
        found && continue
        ord isa Int && return NotElementary(
            "√($uterm): the divisor of the residues$cls is not torsion (its order mod p would be $ord, " *
            "but $ord·Δ is not principal)")
        gen == 1 && return NotElementary(
            "√($uterm): the divisor of the residues$cls has infinite order on the elliptic curve " *
            "(no multiple N ≤ $(last(Ns)) is principal; torsion bound of Mazur / Kamienny–Kenku–Momose)")
        return RischNotImplemented("√($uterm): no multiple N ≤ $(last(Ns)) of the divisor of the residues$cls is " *
                                   "principal on a curve of genus $gen (no torsion order found)")
    end
    out
end

hyp_down_frac(f::QXF) = f
hyp_down_frac(f::Frac{UPoly{QS{d}}}) where {d} = frac(hyp_down(f.num), hyp_down(f.den))

# λ log((p + q y)/G) as a real term. ℚ(√d), d > 0: λ, p, q printed with sqrt(d). d < 0: u ū is a constant
# (div(u ū) = NΔ + conj(NΔ) = 0), so with √d = iδ, u = A + iδB and λ = iδβ: λ log u = -δβ atan(δB/A) + const.
function hyp_log_term(b0::Builder, yterm, d::Int, λ, p, q, G)
    if d > 0 || d == 1
        v = mk(b0, :+, poly_term(b0, p), mk(b0, :*, poly_term(b0, q), yterm))
        lg = mk(b0, :log, isone(G) ? v : mk(b0, :/, v, poly_term(b0, G)))
        return isone(λ) ? lg : mk(b0, :*, cterm(b0, λ), lg)
    end
    δ = -d
    re(f) = QX(Q[c.a for c in f.c])
    im(f) = QX(Q[c.b for c in f.c])
    A = mk(b0, :+, poly_term(b0, re(p)), mk(b0, :*, poly_term(b0, re(q)), yterm))
    B = mk(b0, :+, poly_term(b0, im(p)), mk(b0, :*, poly_term(b0, im(q)), yterm))
    rδ = mk(b0, :sqrt, b0.lift(δ))
    at = mk(b0, :atan, mk(b0, :/, mk(b0, :*, rδ, B), A))
    mk(b0, :*, cterm(b0, QS{δ}(Q(0), -λ.b)), at)
end

# u ū = const·G² (needed for the atan form; for d > 0, so that log u and ½ log(u/ū) agree up to a constant)
function hyp_check_norm(a::QX, d::Int, p, q, G::QX)
    d == 1 && return true
    K = QS{d}
    cj(f) = UPoly{K}(K[K(c.a, -c.b) for c in f.c])
    aK = hyp_lift(K, a)
    pc, qc = cj(p), cj(q)
    iszero(p * qc + pc * q) || return false             # the y-part
    c, z = divrem(hyp_down(p * pc + aK * q * qc), G * G)
    iszero(z) && degree(c) == 0
end

# The hook from `integrate_radical`: one radicand u ∈ ℚ[x] of degree ≥ 3, square roots only.
# radval(ue, e) = the exponent k with ue^e = yᵏ, or nothing.
function integrate_hyperelliptic(f, xk::String, u::QXF, uterm, radval, b0::Builder, verify::Bool)
    a = u.num
    isone(u.den) && degree(a) >= 3 || throw(RischError("integrate_hyperelliptic: not a polynomial radicand"))
    sf = squarefree(a)
    all(((_, m),) -> m == 1, sf) || throw(RischNotImplemented(
        "√($uterm): radicands with repeated factors of degree ≥ 3 are not supported yet"))
    el = parse_hyp(f, xk, u, radval)
    q = el.q
    B, D = q.num * a, q.den                             # q y = q a / y
    g, P, R, D = hyp_reduce(a, B, D)
    # exact check: d(g y) = (g′a + g a′/2)/y must equal q y - (P + R/D)/y, i.e. (q a - P - R/D)/y
    if verify
        dgy = dx(g) * u + g * frac(scale(Q(1) // 2, deriv(a)))
        dgy == q * u - frac(P) - frac(R, D) ||
            throw(RischError("internal check failed: hyperelliptic Hermite reduction"))
    end
    yterm = mk(b0, :sqrt, uterm)
    logt = nothing
    nores(after = "Hermite reduction") = NotElementary(
        "after $after ∫ ($(zpoly_string(P, xk)))/√($uterm) is left: a nonzero differential without " *
        "residues on a curve of genus $(hyp_genus(a))")
    if !(iszero(P) && iszero(R))
        hyp_residue_free(a, P, R) && throw(nores())
        lp = hyp_log_part(a, P, R, D, uterm)
        lp isa Exception && throw(lp)
        W = frac(P) + frac(R, D)
        lts = Any[]
        for (d, λ, pu, qu, G, λPu) in lp
            K = d == 1 ? Q : QS{d}
            if verify
                Pu = hyp_dlog(hyp_lift(K, a), pu, qu)
                hyp_check_dlog(hyp_lift(K, a), pu, qu, hyp_lift(K, G), Pu) && hyp_check_norm(a, d, pu, qu, G) ||
                    throw(RischError("internal check failed: d log((p + q y)/G) on the curve"))
            end
            W = W - λPu
            push!(lts, hyp_log_term(b0, yterm, d, λ, pu, qu, G))
        end
        (isone(W.den) && hyp_residue_free(a, W.num, zero(QX))) ||
            throw(RischError("hyperelliptic log part: residues left after subtracting the logarithms"))
        P = W.num
        iszero(P) || throw(nores("Hermite reduction and the logarithmic part"))
        logt = length(lts) == 1 ? lts[1] : mk(b0, :+, lts...)
    end
    alg = iszero(g) ? nothing : mk(b0, :*, frac_term(b0, g), yterm)
    logt === nothing || (alg = alg === nothing ? logt : mk(b0, :+, alg, logt))
    iszero(el.p) && return alg === nothing ? b0.lift(0) : alg
    T, _ = build_tower(b0.x, xk)
    F = integrate_built(T, el.p, b0, verify)
    alg === nothing && return F
    F isa IntegralWithRootSums && return IntegralWithRootSums(mk(b0, :+, F.elementary, alg), F.rootsums, F.var)
    mk(b0, :+, F, alg)
end
