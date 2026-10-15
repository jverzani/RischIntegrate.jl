# ---------------------------------------------------------------------------
# RootSum: residues that are algebraic of degree > 2 (base level, C = ℚ)
#
# For a residue factor Q(z) (squarefree, no rational roots) left by `log_part` for R/D,
#   Σ_{Q(α)=0} α log W(α, x),   W = gcd(D, R - α D')  in (ℚ[z]/Q)[x], monic in x.
# The gcd is computed by dynamic evaluation (`d5_gcd`): when a leading coefficient is a
# zero divisor mod Q, Q splits (gcd with it) and both parts continue, so Q need not be
# irreducible and no factorisation is needed. Verification is exact in ℚ(x): with the norm
# N = Π_α W(α, x) = res_z(Q, W) and the cofactor N/W (division checked mod Q),
#   d/dx Σ_α α log W(α, x) = Tr_{ℚ[z]/Q}(z · ∂ₓW · N/W) / N,
# the trace through the power sums of the roots of Q (Newton). The result is returned as a
# Risch-owned `RootSum` inside an `IntegralWithRootSums` (the user's packages have no RootSum).
# ---------------------------------------------------------------------------

"""
    RootSum

`Σ_{Q(α)=0} α log W(α, x)`: `poly` is `Q(z)` (monic, squarefree; coefficients low → high) and
`W` the coefficients of `W(z, x)` in `x` (low → high), each a polynomial in `z` reduced mod `Q`.
`var` is how the variable prints and `arg` the term it stands for (after a substitution such as
t = sqrt(1 + x) this is that term; `nothing` when it is the integration variable itself).
Callable: `rs(t)` evaluates the sum numerically at the value `t` of its variable (complex roots,
principal logarithms).
"""
struct RootSum{C}
    poly::UPoly{C}
    W::Vector{UPoly{C}}
    var::String
    arg::Any
end
RootSum{C}(poly, W, var) where {C} = RootSum{C}(poly, W, var, nothing)

"""
    IntegralWithRootSums

An antiderivative `elementary + Σ rootsums` (a term of the user's package plus `RootSum`s, or
`TermRootSum`s for RootSums found inside a tower of exp/log monomials).
`F(a)` evaluates it numerically at a real `a` and returns the real part (the real part of an
antiderivative of a real integrand is an antiderivative too). The logarithms of a RootSum are
continued along the real line from a fixed reference point (not principal values), so `F` is
continuous wherever the integrand is finite and `F(b) - F(a)` is a definite integral.
"""
struct IntegralWithRootSums
    elementary::Any
    rootsums::Vector{Any}            # RootSum (base level) / TermRootSum (inside a tower)
    var::String
end

# coefficients of p (x-poly with coefficients in C[z]) reduced mod m, top zeros dropped
function zmod_trim(m::UPoly{C}, p::Vector{UPoly{C}}) where {C}
    q = UPoly{C}[rem(c, m) for c in p]
    while !isempty(q) && iszero(q[end])
        pop!(q)
    end
    q
end

# p made monic in x modulo m: [(m′, p′)] over a splitting of m (p′ empty: p ≡ 0 mod m′)
function d5_monic(m::UPoly{C}, p::Vector{UPoly{C}}) where {C}
    p = zmod_trim(m, p)
    isempty(p) && return [(m, p)]
    g = monic(gcd(p[end], m))
    if degree(g) == 0
        s, _, g1 = gcdex(p[end], m)                     # s·lc + t·m = g1 ∈ C*
        li = scale_div(s, lc(g1))
        return [(m, zmod_trim(m, UPoly{C}[c * li for c in p]))]
    end
    out = d5_monic(g, p)                                # lc ≡ 0 mod g: the degree drops
    m2 = quo(m, g)
    degree(m2) > 0 && append!(out, d5_monic(m2, p))
    out
end

# a mod b in (C[z]/m)[x], b monic
function d5_rem(m::UPoly{C}, a::Vector{UPoly{C}}, b::Vector{UPoly{C}}) where {C}
    a = copy(a)
    nb = length(b)
    while length(a) >= nb
        c = a[end]
        s = length(a) - nb
        for k in 1:nb
            a[s + k] = a[s + k] - c * b[k]
        end
        a = zmod_trim(m, a)
    end
    a
end

# monic gcd of a and b in (C[z]/m)[x]: [(m′, W)] with m = Π m′
function d5_gcd(m::UPoly{C}, a::Vector{UPoly{C}}, b::Vector{UPoly{C}}) where {C}
    out = Tuple{UPoly{C},Vector{UPoly{C}}}[]
    for (m1, bm) in d5_monic(m, b)
        if isempty(bm)
            append!(out, d5_monic(m1, a))
        else
            append!(out, d5_gcd(m1, bm, d5_rem(m1, a, bm)))
        end
    end
    out
end

# RootSums for an unresolved residue factor (rest, R, D) of `log_part` (D squarefree)
# --- Lazard–Rioboo–Trager (step LR) ------------------------------------------------
# W(α, s) = gcd(D, A - α δD) for the roots α of m, without Euclid in (K[z]/m)[s] (whose coefficients
# swell over function fields such as ℚ(e)). With R(z) = res_s(D, A - z δD) = Π Q_j^j (squarefree),
# a residue of multiplicity j has deg W = j, and W = S_j(α, s), S_j the subresultant of degree j of
# D and A - z δD (Bronstein, IntRationalLogPart), after removing the content of S_j that vanishes
# on Q_j: S_j / Π_k gcd(L_k, Q_j)^k, lc_s(S_j) = Π L_k^k (squarefree). S_j is computed by
# evaluation at z = 0, 1, 2, … (determinants over K) and interpolation: its coefficients have
# degree ≤ deg D - j in z. Then reduced mod m_j = gcd(m, Q_j) and made monic (`d5_monic`). Returns
# [(m′, W)] like `d5_gcd`, or nothing (the caller then uses `d5_gcd`).

# determinant over a field by Bareiss's fraction-free elimination: every division is exact, so
# entries that are polynomials (e.g. in e, when K = ℚ(e)) stay polynomials of bounded size instead
# of becoming growing rational functions as in Gaussian elimination
function field_det(M::Matrix{K}) where {K}
    M = copy(M)
    n = size(M, 1)
    n == 0 && return one(K)
    sgn = 1
    prev = one(K)
    for c in 1:(n - 1)
        if iszero(M[c, c])
            r = findfirst(k -> !iszero(M[k, c]), (c + 1):n)
            r === nothing && return zero(K)
            r += c
            M[c, :], M[r, :] = M[r, :], M[c, :]
            sgn = -sgn
        end
        for k in (c + 1):n, l in (c + 1):n
            M[k, l] = (M[c, c] * M[k, l] - M[k, c] * M[c, l]) / prev
        end
        prev = M[c, c]
    end
    sgn == 1 ? M[n, n] : -M[n, n]
end

# coefficients (s^0 … s^j) of the subresultant of degree j of P (degree m) and Q (degree n), j < m
function subresultant_coeffs(P::UPoly{K}, Q::UPoly{K}, j::Int) where {K}
    m, n = degree(P), degree(Q)
    N = m + n - j                                       # powers s^0 … s^(N-1)
    rows = Vector{K}[]
    for k in 0:(n - j - 1)
        r = fill(zero(K), N)
        for (l, c) in enumerate(P.c)
            r[k + l] = c
        end
        push!(rows, r)
    end
    for k in 0:(m - j - 1)
        r = fill(zero(K), N)
        for (l, c) in enumerate(Q.c)
            r[k + l] = c
        end
        push!(rows, r)
    end
    hi = collect((N - 1):-1:(j + 1))                    # power indices of the fixed columns
    out = K[]
    for i in 0:j
        cols = vcat(hi, i)
        push!(out, isempty(rows) ? zero(K) : field_det(K[rows[r][c + 1] for r in eachindex(rows), c in cols]))
    end
    out
end

function lrt_logs(m::UPoly{K}, D::UPoly{K}, A::UPoly{K}, dD::UPoly{K}) where {K}
    P = UPoly{K}
    mdeg = degree(D)
    n = max(length(A.c), length(dD.c))
    ai(k) = k <= length(A.c) ? A.c[k] : zero(K)
    di(k) = k <= length(dD.c) ? dD.c[k] : zero(K)
    Bat(z) = P(K[ai(k) - z * di(k) for k in 1:n])
    Rz = residue_resultant(D, A, dD)
    out = Tuple{P,Vector{P}}[]
    covered = one(P)
    for (Qj, j) in squarefree(Rz)
        mj = gcd(monic(m), Qj)
        degree(mj) > 0 || continue
        covered = covered * mj
        if j == mdeg
            S = P[P(K[c]) for c in D.c]
        elseif j > mdeg
            return nothing
        else
            zs, vals = K[], Vector{K}[]
            t = 0
            while length(zs) <= mdeg - j
                z = t * one(K)
                t += 1
                B = Bat(z)
                length(B.c) == n || continue
                push!(zs, z)
                push!(vals, subresultant_coeffs(D, B, j))
            end
            S = P[interpolate(zs, K[v[i] for v in vals]) for i in 1:(j + 1)]
            for (L, k) in squarefree(S[end])            # content vanishing on Q_j
                g = gcd(L, Qj)
                degree(g) > 0 || continue
                gk = g^k
                for l in eachindex(S)
                    q, r = divrem(S[l], gk)
                    iszero(r) || return nothing
                    S[l] = q
                end
            end
        end
        for (m2, W) in d5_monic(mj, S)
            length(W) == j + 1 || return nothing
            push!(out, (m2, W))
        end
    end
    degree(covered) == degree(m) ? out : nothing
end

function root_sums(rest::UPoly{C}, R::UPoly{C}, D::UPoly{C}, var::String; arg = nothing) where {C}
    P = UPoly{C}
    dD = deriv(D)
    n = max(length(R.c), length(dD.c))
    ri(i) = i <= length(R.c) ? R.c[i] : zero(C)
    di(i) = i <= length(dD.c) ? dD.c[i] : zero(C)
    a = P[P(C[c]) for c in D.c]
    b = P[P(C[ri(i), -di(i)]) for i in 1:n]             # R - z D'
    out = RootSum{C}[]
    lr = lrt_logs(monic(rest), D, R, dD)
    for (m, W) in (lr === nothing ? d5_gcd(monic(rest), a, b) : lr)
        length(W) >= 2 || throw(RischError("RootSum: trivial gcd for a residue factor"))
        push!(out, RootSum{C}(m, W, var, arg))
    end
    out
end

# power sums p_k = Σ α^k (k = 0 … n-1) of the roots of the monic m (Newton's identities)
function power_sums(m::UPoly{C}) where {C}
    n = degree(m)
    e(i) = m.c[n + 1 - i]                               # coefficient of z^(n-i): (-1)^i e_i
    p = C[cfromQ(C, Q(n))]
    for k in 1:(n - 1)
        s = cfromQ(C, Q(k)) * e(k)
        for i in 1:(k - 1)
            s = s + e(i) * p[k - i + 1]
        end
        push!(p, -s)
    end
    p
end
ztrace(ps, g::UPoly{C}) where {C} = isempty(g.c) ? zero(C) : sum(g.c[k] * ps[k] for k in eachindex(g.c))

# exact d/dx of the RootSum in C(x)
function rootsum_derivative(rs::RootSum{C}) where {C}
    m, W = rs.poly, rs.W
    P = UPoly{C}
    K = Frac{P}
    xp = xpoly(C)
    nz = degree(m)
    Wz = UPoly{K}(K[frac(sum(scale(j <= length(W[k].c) ? W[k].c[j] : zero(C), xp^(k - 1)) for k in eachindex(W)))
                    for j in 1:nz])
    Nr = resultant(UPoly{K}(K[kconst(c) for c in m.c]), Wz)       # Π_α W(α, x), m monic
    isone(Nr.den) || throw(RischError("RootSum: the norm is not a polynomial"))
    N = Nr.num
    Nv = P[P(C[c]) for c in N.c]
    rest = copy(Nv)                                                # N = W · cof mod m
    cof = [zero(P) for _ in 1:(length(Nv) - length(W) + 1)]
    while length(rest) >= length(W)
        c = rest[end]
        s = length(rest) - length(W)
        cof[s + 1] = c
        for k in eachindex(W)
            rest[s + k] = rest[s + k] - c * W[k]
        end
        rest = zmod_trim(m, rest)
    end
    isempty(rest) || throw(RischError("RootSum: W(α, x) does not divide its norm"))
    dW = P[scale(cfromQ(C, Q(k - 1)), W[k]) for k in 2:length(W)]
    zP = P(C[zero(C), one(C)])
    ps = power_sums(m)
    num = zero(P)
    for (i, u) in enumerate(dW), (j, v) in enumerate(cof)
        num = num + scale(ztrace(ps, rem(zP * u * v, m)), xp^(i + j - 2))
    end
    frac(num, N)
end
