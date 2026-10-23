# --- RootSums inside towers (step RT) ---------------------------------------------
# At level i (θ = θᵢ, K = Kᵢ₋₁): Σ_{m(α)=0} α log W(α, θ), W = gcd(D, A - α δD) in (K[z]/m)[θ]
# monic in θ (`d5_gcd` over K: ℚ is algebraically closed in K, so a split of m is over ℚ). W is
# stored θ-major (W[k]: coefficient of θ^(k-1), a polynomial in z over K, reduced mod m). The
# exact derivative is computed as for the base (`rootsum_derivative`), with the tower derivation:
#   δW = Σ_k (δc_k) θ^(k-1) + ∂_θW · Dθ   (z is a constant),   Σ α δW/W = Tr(z·δW·N/W)/N.
struct TowerRootSum
    i::Int
    mq::UPoly                # m, monic, over the constant field C (ℚ or ℚ(i))
    W::Vector{Any}           # Vector{UPoly{K}}
    deriv::Any               # exact derivative ∈ Kᵢ
end
# a base-level RootSum (in x) inside a tower; W in x as in `RootSum`
struct BaseRootSum
    rs::RootSum
    deriv::Any               # ∈ K₀ = ℚ(x)
end
# exp correction: Σ_α α·deg_θ W = Tr(α)·deg W
rootsum_corr(q::TowerRootSum) = (length(q.W) - 1) * (-q.mq.c[end - 1])

function tower_root_sums(T::Tower{C}, i::Int, A::UPoly{K}, D::UPoly{K}, dD::UPoly{K}, rest::UPoly{C}) where {C,K}
    cdepth(C) > MAX_ROOTSUM_GENS && degree(rest) > 2 && throw(RischNotImplemented(
        "a RootSum over more than $MAX_ROOTSUM_GENS symbolic constants (parameters)"))
    P = UPoly{K}
    mK = P(K[lconst(T, c, i - 1) for c in monic(rest).c])
    n = max(length(A.c), length(dD.c))
    ai(k) = k <= length(A.c) ? A.c[k] : zero(K)
    di(k) = k <= length(dD.c) ? dD.c[k] : zero(K)
    a = P[P(K[c]) for c in D.c]
    b = P[P(K[ai(k), -di(k)]) for k in 1:n]             # A - z δD
    out = Any[]
    lr = lrt_logs(mK, D, A, dD)
    for (m, W) in (lr === nothing ? d5_gcd(mK, a, b) : lr)
        length(W) >= 2 || throw(RischError("RootSum: trivial gcd for a residue factor"))
        cs = C[]
        for c in m.c
            v = dconst_value(T, c)
            v === nothing && throw(RischNotImplemented("RootSum: a split of the residue polynomial is not over C"))
            push!(cs, v)
        end
        mq = UPoly{C}(cs)
        push!(out, TowerRootSum(i, mq, W, tower_rootsum_derivative(T, i, m, mq, W)))
    end
    out
end

function tower_rootsum_derivative(T::Tower, i::Int, m::UPoly{K}, mq::UPoly, W::Vector) where {K}
    P = UPoly{K}
    F = T.Ts[i + 1]                                     # Kᵢ
    θ = xpoly(K)
    nz = degree(m)
    # norm N(θ) = Π_α W(α, θ) = res_z(m, W(z, θ)) (m monic): degree ≤ deg m · deg_θ W in θ, so it is
    # interpolated from resultants over K at θ = 0, 1, 2, … (Euclid over Kᵢ = K(θ) swells, step ST)
    θs, vals = K[], K[]
    for t in 0:(nz * (length(W) - 1))
        θ0 = t * one(K)
        Wt = P(K[sum((j <= length(W[k].c) ? W[k].c[j] : zero(K)) * θ0^(k - 1) for k in eachindex(W)) for j in 1:nz])
        push!(θs, θ0)
        push!(vals, resultant(m, Wt))
    end
    N = interpolate(θs, vals)
    rest = P[P(K[c]) for c in N.c]                                    # N = W · cof mod m
    cof = [zero(P) for _ in 1:(length(rest) - length(W) + 1)]
    while length(rest) >= length(W)
        c = rest[end]
        s = length(rest) - length(W)
        cof[s + 1] = c
        for k in eachindex(W)
            rest[s + k] = rest[s + k] - c * W[k]
        end
        rest = zmod_trim(m, rest)
    end
    isempty(rest) || throw(RischError("RootSum: W(α, θ) does not divide its norm"))
    dθ = T.levels[i].dtheta
    dW = [P(K[D(T, i - 1, e) for e in W[k].c]) for k in eachindex(W)]
    for k in 2:length(W), (l, e) in enumerate(dθ.c)
        idx = k - 2 + l
        while length(dW) < idx
            push!(dW, zero(P))
        end
        dW[idx] = dW[idx] + scale(e * lq(T, Q(k - 1), i - 1), W[k])
    end
    dW = zmod_trim(m, dW)
    zP = P(K[zero(K), one(K)])
    ps = [lconst(T, c, i - 1) for c in power_sums(mq)]
    num = zero(P)
    for (a, u) in enumerate(dW), (b, v) in enumerate(cof)
        num = num + scale(ztrace(ps, rem(zP * u * v, m)), θ^(a + b - 2))
    end
    frac(num, N)
end

"""
    TermRootSum

`Σ_{Q(α)=0} α log W(α)` with `W(α) = Σ_j coeffs[j] α^(j-1)`, the `coeffs` being terms of the
user's package (a RootSum found inside a tower, e.g. in log(x)). `rs(a)` evaluates numerically
at x = a.
"""
struct TermRootSum
    poly::UPoly              # over ℚ, or ℚ(i) (then each coefficient is a pair (re, im) of terms)
    coeffs::Vector{Any}
    var::String
    pterms::Any              # nothing, or the coefficients of poly as terms (constants e, log 2, …)
end
TermRootSum(poly, coeffs, var) = TermRootSum(poly, coeffs, var, nothing)

# a base-level RootSum over C = ℚ(t₁, …) as a TermRootSum (step RE): α-coefficients are polynomials
# in x over C, printed with `poly_term`; the polynomial's coefficients are terms too
function base_term_rootsum(b::Builder, rs::RootSum{C}) where {C}
    xp = xpoly(C)
    if real_param_field(C) && degree(rs.poly) == 2         # step PQ
        Uz = [sum((j <= length(rs.W[k].c) ? scale(rs.W[k].c[j], xp^(k - 1)) : zero(UPoly{C})) for k in eachindex(rs.W))
              for j in 1:2]
        return param_quad_term(b, rs.poly, Uz[1], Uz[2], (c, e) -> scale(c, e), e -> poly_term(b, e))
    end
    cs = Any[]
    for j in 1:degree(rs.poly)
        p = sum((j <= length(rs.W[k].c) ? scale(rs.W[k].c[j], xp^(k - 1)) : zero(UPoly{C})) for k in eachindex(rs.W))
        push!(cs, iszero(p) ? nothing : poly_term(b, p))
    end
    TermRootSum(rs.poly, cs, string(b.x), Any[cterm(b, c) for c in rs.poly.c])
end
function TermRootSum(b::Builder, T::Tower, q::TowerRootSum)
    C = ctype(T)
    if real_param_field(C) && degree(q.mq) == 2           # step PQ
        K = T.Ts[q.i]
        P = UPoly{K}
        Uz = [P(K[j <= length(q.W[k].c) ? q.W[k].c[j] : zero(K) for k in eachindex(q.W)]) for j in 1:2]
        return param_quad_term(b, q.mq, Uz[1], Uz[2], (c, e) -> scale(lconst(T, c, q.i - 1), e),
                               e -> tower_to_term(b, T, frac(e)))
    end
    pt = (C === Q || C === QI) ? nothing : Any[cterm(b, c) for c in q.mq.c]
    K = T.Ts[q.i]
    P = UPoly{K}
    W = q.W
    cs = Any[]
    for j in 1:degree(q.mq)
        cz = P(K[j <= length(W[k].c) ? W[k].c[j] : zero(K) for k in eachindex(W)])
        push!(cs, iszero(cz) ? nothing : tower_to_term(b, T, frac(cz)))
    end
    TermRootSum(q.mq, cs, string(b.x), pt)
end

# a RootSum over ℚ(i) (trig tower, step RC): each α-coefficient w (an element of level i, or of
# ℚ(i)(x) for a base-level RootSum) is written as R + i·I with R = (w + σw)/2, I = (w - σw)/(2i)
# σ-invariant, i.e. real terms (`real_term`)
function complex_term_rootsum(b::Builder, T::Tower, kinds, q)
    C = ctype(T)
    if q isa BaseRootSum
        i, mq, W = 0, q.rs.poly, q.rs.W
        xp = xpoly(C)
        ws = [frac(sum((j <= length(W[k].c) ? scale(W[k].c[j], xp^(k - 1)) : zero(UPoly{C})) for k in eachindex(W)))
              for j in 1:degree(mq)]
    else
        i, mq, W = q.i, q.mq, q.W
        K = T.Ts[i]
        ws = [frac(UPoly{K}(K[j <= length(W[k].c) ? W[k].c[j] : zero(K) for k in eachindex(W)])) for j in 1:degree(mq)]
    end
    half = lconst(T, inv(cfromQ(C, Q(2))), i)
    inv2i = lconst(T, inv(cimag(C) + cimag(C)), i)
    cs = Any[]
    for w in ws
        sw = tconj(T, kinds, w, i)
        R, I = (w + sw) * half, (w - sw) * inv2i
        push!(cs, (iszero(R) ? nothing : real_term(b, T, kinds, R, i), iszero(I) ? nothing : real_term(b, T, kinds, I, i)))
    end
    TermRootSum(mq, cs, string(b.x))
end

# step PQ: a RootSum over m(z) = z² + p z + q irreducible over a real parameter field C = ℚ(a, …), with
# W(α) = U + αV, written out. With α = m₀ ± w, m₀ = -p/2, w² = δ = m₀² - q, P₀ = U + m₀V:
#   Σ α log(U + αV) = m₀ log(U² - pUV + qV²) + w log((P₀ + wV)/(P₀ - wV))
#                   = m₀ log(…) - 2σ atan(σV/P₀)            (δ = -σ²)
# σ ∈ C when -δ is a square; else σ = √(-δ) or √δ as a term, the sign of δ taken at the parameter values
# of `param_value` (a = 1, b = 2, …; either form is an antiderivative, real for its sign of δ).
# U, V are polynomials (in x, or in θ over K); sc(c, P) scales by c ∈ C, tt(P) gives the term.
function param_quad_term(b::Builder, mq::UPoly{C}, U, V, sc, tt) where {C}
    q, p = monic(mq).c[1], monic(mq).c[2]
    m0 = -p * cfromQ(C, Q(1, 2))
    δ = m0 * m0 - q
    P0 = U + sc(m0, V)
    ts = Any[]
    if !iszero(m0)
        N = U * U - sc(p, U * V) + sc(q, V * V)
        push!(ts, mk(b, :*, cterm(b, m0), mk(b, :log, tt(N))))
    end
    # -2σ atan(σV/P₀), or 2σ atan(P₀/(σV)) (the same derivative), continuous when V is a constant
    vconst = degree(V) <= 0
    σ = csqrt(-δ)
    dv = σ === nothing ? param_value(δ, b.consts) : nothing
    if σ === nothing && dv !== nothing && dv > 0
        st = csqrt_term(b, δ)
        sV = mk(b, :*, st, tt(V))
        push!(ts, mk(b, :*, st, mk(b, :log, mk(b, :/, mk(b, :+, tt(P0), sV),
                                                   mk(b, :+, tt(P0), mk(b, :*, b.lift(-1), sV))))))
    else
        st = σ !== nothing ? cterm(b, σ) : csqrt_term(b, -δ)
        sV = σ !== nothing ? tt(sc(σ, V)) : mk(b, :*, st, tt(V))
        push!(ts, vconst ? mk(b, :*, b.lift(2), st, mk(b, :atan, mk(b, :/, tt(P0), sV))) :
                           mk(b, :*, b.lift(-2), st, mk(b, :atan, mk(b, :/, sV, tt(P0)))))
    end
    length(ts) == 1 ? ts[1] : mk(b, :+, ts...)
end
real_param_field(::Type{C}) where {C} = C <: Frac && rational_tfield(C) && cbase(C) === Q

# √c for c ∈ C = B(t) as a term, with a square numerator or denominator (in t) taken out
function csqrt_term(b::Builder, c::Frac{<:UPoly})
    n, d = frac(c.num), frac(c.den)
    sn, sd = csqrt(n), csqrt(d)
    if sn === nothing && sd === nothing && (csqrt(-n) !== nothing || csqrt(-d) !== nothing)
        n, d = -n, -d                                    # c = (-n)/(-d)
        sn, sd = csqrt(n), csqrt(d)
    end
    nt = sn === nothing ? mk(b, :sqrt, cterm(b, n)) : cterm(b, sn)
    sd === nothing && sn !== nothing && return mk(b, :/, nt, mk(b, :sqrt, cterm(b, d)))
    sd === nothing && return mk(b, :sqrt, cterm(b, c))
    isone(sd) ? nt : mk(b, :/, nt, cterm(b, sd))
end
csqrt_term(b::Builder, c) = mk(b, :sqrt, cterm(b, c))
