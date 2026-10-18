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

# p + q y in ℚ(x)(y), y² = a
struct HypEl
    p::QXF
    q::QXF
end
Base.:(==)(f::HypEl, g::HypEl) = f.p == g.p && f.q == g.q
hyp_add(f::HypEl, g::HypEl) = HypEl(f.p + g.p, f.q + g.q)
hyp_neg(f::HypEl) = HypEl(-f.p, -f.q)
hyp_mul(a::QXF, f::HypEl, g::HypEl) = HypEl(f.p * g.p + a * f.q * g.q, f.p * g.q + f.q * g.p)
function hyp_inv(a::QXF, f::HypEl)
    n = f.p * f.p - a * f.q * f.q                       # norm; nonzero since a is not a square
    iszero(n) && throw(DivideError())
    HypEl(f.p / n, -f.q / n)
end
function hyp_pow(a::QXF, f::HypEl, k::Integer)
    k < 0 && return hyp_pow(a, hyp_inv(a, f), -k)
    r, b = HypEl(one(QXF), zero(QXF)), f
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
            v = HypEl[parse_hyp(u, xk, a, radval) for u in args]
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

# d(log u) = Pu/y for u = (p + q y)/G (G ∈ ℚ[x]), when N = p² - a q² = c·G²: the rational part
# N′/(2N) - G′/G vanishes and Pu = (p (q′a + q a′/2) - p′q a)/N
function hyp_dlog(a::QX, p::QX, q::QX)
    frac(p * (deriv(q) * a + scale(Q(1) // 2, q * deriv(a))) - deriv(p) * q * a, p * p - a * q * q)
end

# exact check of d(log u) = Pu/y, u = (p + q y)/G, in ℚ(x)(y)
function hyp_check_dlog(a::QX, p::QX, q::QX, G::QX, Pu::QXF)
    A = frac(a)
    up, uq = frac(p, G), frac(q, G)
    du = HypEl(dx(up), dx(uq) + uq * frac(scale(Q(1) // 2, deriv(a))) / A)
    hyp_mul(A, du, hyp_inv(A, HypEl(up, uq))) == HypEl(zero(QXF), Pu / A)
end

hyp_invmod(M::P, V::P) where {P<:UPoly} = hyp_solve_mod(one(P), M, V)

# ℤ/pℤ, p = 2³¹ - 1: a field for UPoly, used to filter linear systems (a trivial kernel mod p
# implies a trivial kernel over ℚ: reduction mod p can only lower the rank)
const HYP_P = 2147483647
struct ModP
    v::Int
end
modp(n::Integer) = ModP(Int(mod(n, HYP_P)))
function modp(q::Q)                                    # nothing when p divides the denominator
    d = mod(denominator(q), HYP_P)
    iszero(d) ? nothing : modp(numerator(q)) * inv(ModP(Int(d)))
end
Base.zero(::Type{ModP}) = ModP(0)
Base.one(::Type{ModP}) = ModP(1)
Base.zero(::ModP) = ModP(0)
Base.one(::ModP) = ModP(1)
Base.iszero(a::ModP) = a.v == 0
Base.isone(a::ModP) = a.v == 1
Base.:+(a::ModP, b::ModP) = ModP(mod(a.v + b.v, HYP_P))
Base.:-(a::ModP, b::ModP) = ModP(mod(a.v - b.v, HYP_P))
Base.:-(a::ModP) = ModP(mod(-a.v, HYP_P))
Base.:*(a::ModP, b::ModP) = ModP(mod(a.v * b.v, HYP_P))
Base.:*(n::Integer, a::ModP) = modp(n) * a
Base.inv(a::ModP) = iszero(a) ? throw(DivideError()) : ModP(powermod(a.v, HYP_P - 2, HYP_P))
Base.:/(a::ModP, b::ModP) = a * inv(b)

# p ∈ ℚ[x] mod p (nothing if a denominator vanishes)
function modp(p::QX)
    c = ModP[]
    for a in p.c
        m = modp(a)
        m === nothing && return nothing
        push!(c, m)
    end
    UPoly{ModP}(c)
end

# The finite residues of (P + R/D)/y (D squarefree, coprime to a and R): [(G, r, S)] with r > 0, G the
# product of the irreducible factors of D whose places carry the residues ±r, and S ≡ R/(r D′) mod G
# (y ≡ S at the places of residue r, y ≡ -S at those of residue -r). `nothing` when a residue is
# irrational. Over the roots α of a factor F: res = R(α)/(D′(α) y(α)), so res² ≡ R²/(D′² a) mod F.
function hyp_finite_residues(a::QX, R::QX, D::QX)
    dD = deriv(D)
    byr = Dict{Q,QX}()
    for F in factor_Q(D)
        h = rem(R * R * hyp_invmod(dD * dD * a, F), F)
        degree(h) <= 0 || return nothing
        r = rat_sqrt(isempty(h.c) ? Q(0) : h.c[1])
        (r === nothing || iszero(r)) && return nothing
        byr[r] = get(byr, r, one(QX)) * F
    end
    [(G, r, rem(R * hyp_invmod(scale(r, dD), G), G)) for (r, G) in byr]
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

# v = p + q y with div(v) ≥ Σ 2N nᵢ P_{rᵢ} - o₊∞₊ - o₋∞₋ (o± = M/2 ∓ N n∞, M = Σ 2N nᵢ deg Gᵢ; for deg a
# odd the single place at infinity, pole order ≤ M). The divisor has degree 0, so the solutions form a
# space of dimension ≤ 1, and dimension 1 iff N·Δ is principal (Δ = Σ nᵢ(P_{rᵢ} - σP_{rᵢ}) +
# n∞(∞₊ - ∞₋)): then (p, q), with p² - a q² = c·Π Gᵢ^(2N nᵢ); else nothing.
# res = [(Gᵢ, nᵢ, Sᵢ)]; l = √lc(a) (used only when n∞ ≠ 0).
function hyp_divisor_unit(a::QX, res, ninf::Int, l, N::Int; maxsize::Int = 1500)
    na = degree(a)
    es = [2N * n for (_, n, _) in res]
    M = sum(es[i] * degree(res[i][1]) for i in eachindex(res))
    if isodd(na)
        dp, dq = fld(M, 2), fld(M - na, 2)
        conds = Tuple{Int,Int}[]                        # (branch sign, pole order)
    else
        m = na ÷ 2
        op, om = M ÷ 2 - N * ninf, M ÷ 2 + N * ninf
        omax = max(op, om)
        dp, dq = omax, omax - m
        conds = ninf == 0 ? Tuple{Int,Int}[] : [(op < om ? 1 : -1, min(op, om))]
    end
    (dp < 0 && dq < 0) && return nothing
    dp + dq + 2 > maxsize && return :toolarge
    s = isempty(conds) ? Q[] : hyp_sqrt_series(a, max(dq, 0) + na ÷ 2 - conds[1][2] + 1, Q(1, 2))   # y
    # filter mod p first, then the exact system over ℚ
    sp = isempty(conds) ? ModP[] : modp.(s)
    ap, lp = modp(a), l === nothing ? nothing : modp(l)
    resp = [(modp(G), n, modp(S)) for (G, n, S) in res]
    ok = !any(isnothing, sp) && ap !== nothing && !(l !== nothing && lp === nothing) &&
         all(r -> r[1] !== nothing && r[3] !== nothing, resp)
    if ok
        colsp = hyp_divisor_cols(ap, resp, es, conds, sp, lp, dp, dq)
        isempty(nullspace_cols(colsp, length(colsp))) && return nothing
    end
    cols = hyp_divisor_cols(a, res, es, conds, s, l, dp, dq)
    ker = nullspace_cols(cols, length(cols))
    isempty(ker) && return nothing
    v = ker[1]
    np = max(dp + 1, 0)
    p, q = QX(v[1:np]), QX(v[(np + 1):end])
    Gn = prod(res[i][1]^es[i] for i in eachindex(res))
    c, z = divrem(p * p - a * q * q, Gn)
    (iszero(z) && degree(c) == 0) || throw(RischError("hyp_divisor_unit: the norm is not c·ΠGᵢ^(2N nᵢ)"))
    cs = vcat(p.c, q.c)                                 # primitive, integer coefficients
    k = Q(lcm(denominator.(cs)...)) / Q(gcd(numerator.(cs)...))
    # sign: the dominant term of p + q y at x → +∞ (y > 0) positive, so log's argument is positive there
    dom = (iszero(q) || (!iszero(p) && 2 * degree(p) >= 2 * degree(q) + na)) ? p : q
    lc(dom) < 0 && (k = -k)
    scale(k, p), scale(k, q)
end

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

# The log part of (P + R/D)/y (simple poles, some residue ≠ 0): (λ, p, q, G, Pu) with
# d(λ log((p + q y)/G)) = λ Pu/y and the same residues; or the exception to raise. Residues only at
# ∞± (R = 0): the polynomial Pell equation. Otherwise all residues must be rational: with b their
# gcd, Δ = Σ (r/b)(P_r - σP_r) + (ρ₊/b)(∞₊ - ∞₋) and the least N with N·Δ principal (λ = b/N).
# Genus 1: Δ is a ℚ-point of the Jacobian, an elliptic curve over ℚ, so N ≤ 12 (Mazur) decides.
function hyp_log_part(a::QX, P::QX, R::QX, D::QX, uterm)
    gen = hyp_genus(a)
    Nmax = 12
    na = degree(a)
    ρ = isodd(na) ? Q(0) : hyp_res_inf(a, P)            # √lc(a) · (−residue at ∞₊)
    l = isodd(na) ? nothing : rat_sqrt(lc(a))
    if iszero(R)
        pq = hyp_pell(a; maxdeg = gen == 1 ? Nmax : 60)
        pq === :none && gen == 1 && return NotElementary(
            "√($uterm): the residues are at ∞₊, ∞₋ only, and ∞₊ - ∞₋ has infinite order on the elliptic " *
            "curve (no unit p + q√a with deg p ≤ 12, Mazur's bound)")
        pq isa Tuple || return RischNotImplemented(
            "√($uterm): residues at infinity, but no unit p + q√a found (polynomial Pell equation " *
            "p² - a q² = c; search bound reached on a curve of genus $gen, no torsion bound yet)")
        pu, qu = pq
        Pu = hyp_dlog(a, pu, qu)
        return hyp_res_inf(a, P) / hyp_res_inf(a, Pu.num), pu, qu, one(QX), Pu
    end
    fin = hyp_finite_residues(a, R, D)
    (fin === nothing || (!iszero(ρ) && l === nothing)) && return RischNotImplemented(
        "√($uterm): irrational residues; the logarithmic part on a curve of genus $gen needs " *
        "algebraic residues (not implemented yet)")
    ρinf = iszero(ρ) ? Q(0) : -ρ / l                    # the residue at ∞₊
    b = reduce(gcd, vcat([r for (_, r, _) in fin], iszero(ρinf) ? Q[] : [abs(ρinf)]))
    res = [(G, Int(r / b), S) for (G, r, S) in fin]
    ninf = Int(ρinf / b)
    for N in 1:Nmax
        pq = hyp_divisor_unit(a, res, ninf, l, N)
        pq === nothing && continue
        pq === :toolarge && return RischNotImplemented(
            "√($uterm): the divisor of the residues is too large for the search (multiple N = $N)")
        pu, qu = pq
        G = prod(Gi^(N * n) for (Gi, n, _) in res)
        return b / N, pu, qu, G, hyp_dlog(a, pu, qu)
    end
    gen == 1 && return NotElementary(
        "√($uterm): the divisor of the residues has infinite order on the elliptic curve " *
        "(no multiple N ≤ 12 is principal, Mazur's bound)")
    RischNotImplemented("√($uterm): no multiple N ≤ $Nmax of the divisor of the residues is principal on a " *
                        "curve of genus $gen (no torsion bound yet)")
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
    nores() = NotElementary("after Hermite reduction ∫ ($(zpoly_string(P, xk)))/√($uterm) is left: a nonzero " *
                            "differential without residues on a curve of genus $(hyp_genus(a))")
    if !(iszero(P) && iszero(R))
        hyp_residue_free(a, P, R) && throw(nores())
        lp = hyp_log_part(a, P, R, D, uterm)
        lp isa Exception && throw(lp)
        λ, pu, qu, G, Pu = lp
        verify && !hyp_check_dlog(a, pu, qu, G, Pu) &&
            throw(RischError("internal check failed: d log((p + q y)/G) on the curve"))
        W = frac(P) + frac(R, D) - Pu * kconst(λ)
        (isone(W.den) && hyp_residue_free(a, W.num, zero(QX))) ||
            throw(RischError("hyperelliptic log part: residues left after subtracting the logarithm"))
        P = W.num
        iszero(P) || throw(nores())
        v = mk(b0, :+, poly_term(b0, pu), mk(b0, :*, poly_term(b0, qu), yterm))
        lg = mk(b0, :log, isone(G) ? v : mk(b0, :/, v, poly_term(b0, G)))
        logt = isone(λ) ? lg : mk(b0, :*, cterm(b0, λ), lg)
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
