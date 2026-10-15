# ---------------------------------------------------------------------------
# Step 9d: the parametric Risch DE in towers (Bronstein 7.1)
#
#   y' + f y = Σ cᵢ gᵢ,    y ∈ K_m,  c = (c₁, …, c_r) ∈ C^r unknown
#
# The solutions (y, c) form a finite-dimensional C-vector space; `prde` returns a basis
# [(y, c)] of it, or `nothing` when a case is not handled (an undecided cancellation case, a
# weak normaliser with a huge residue): callers must not conclude anything from `nothing`.
# The steps are those of `rde_general`; every condition "Σ cᵢ (something) = 0" becomes a linear
# constraint on c over C (`c_nullspace`, through the C-coordinates `cflat_c`), and the problem is
# re-parametrised on the solution space of the constraint (c = Σ c'ⱼ Nⱼ):
#   0. weak normalisation: y = z/q;
#   1. normal denominator h (every solution has normal denominator dividing h, f weakly
#      normalised); a q' + b q = Σ cᵢ Cᵢ with Cᵢ = d_n h² gᵢ;
#   2. the normal poles left in Σ cᵢ Cᵢ must cancel (constraint);
#   3. special denominator (exp: lowest power of t, with the cancellation exponent);
#   4. degree bound (`rde_degree_bound`);
#   5. parametric SPDE (`prde_spde`): q = α h + Σ c'ⱼ βⱼ with h' + b̄ h = Σ c'ⱼ C̄ⱼ;
#   6. polynomial solutions (`prde_poly`): deg b̄ > 0 top-down (linear in the right-hand sides);
#      b̄ ∈ k one coefficient of h at a time, top-down, each a parametric RDE in k (recursion)
#      whose parameters are the current solution basis (log: the coupling term -(s+1) h_(s+1) t'
#      is part of each right-hand side). This also covers b̄ = 0 (integration, where k's
#      constants are the homogeneous solutions) and the cancellation cases (the recursive call
#      returns the homogeneous solutions in k), so no logarithmic-derivative test is needed here.
# Every basis element is verified exactly.
# ---------------------------------------------------------------------------

# C-coordinates of elements of K_l (aligned across the list): C-linear relations among the
# elements are exactly those among the vectors (as `flat`, stopping at C instead of ℚ)
function cflat_c(T::Tower{C}, l::Int, elems) where {C}
    isempty(elems) && return Vector{C}[]
    L = reduce(plcm, [e.den for e in elems]; init = one(typeof(first(elems).den)))
    nums = [e.num * quo(L, e.den) for e in elems]
    n = maximum(length(p.c) for p in nums)
    K = l == 0 ? C : T.Ts[l]
    parts = [begin
                 col = K[k <= length(p.c) ? p.c[k] : zero(K) for p in nums]
                 l == 0 ? [C[c] for c in col] : cflat_c(T, l - 1, col)
             end for k in 1:n]
    [reduce(vcat, (parts[k][j] for k in 1:n); init = C[]) for j in eachindex(elems)]
end

# a basis of {c ∈ S^r : Σ cⱼ vⱼ = 0} (the vⱼ of equal length)
function nullspace_cols(vs::Vector{Vector{S}}, r::Int) where {S}
    nrow = r == 0 ? 0 : length(vs[1])
    M = S[vs[j][i] for i in 1:nrow, j in 1:r]
    piv = Int[]
    row = 1
    for col in 1:r
        row > nrow && break
        p = findfirst(i -> !iszero(M[i, col]), row:nrow)
        p === nothing && continue
        p += row - 1
        if p != row
            for j in 1:r
                M[row, j], M[p, j] = M[p, j], M[row, j]
            end
        end
        pv = inv(M[row, col])
        for j in 1:r
            M[row, j] = M[row, j] * pv
        end
        for i in 1:nrow
            (i == row || iszero(M[i, col])) && continue
            fct = M[i, col]
            for j in 1:r
                M[i, j] = M[i, j] - fct * M[row, j]
            end
        end
        push!(piv, col)
        row += 1
    end
    basis = Vector{S}[]
    for fc in 1:r
        fc in piv && continue
        v = fill(zero(S), r)
        v[fc] = one(S)
        for (i, pc) in enumerate(piv)
            v[pc] = -M[i, fc]
        end
        push!(basis, v)
    end
    basis
end

# a basis of the c ∈ C^r with Σ cᵢ eᵢ = 0, eᵢ elements of K_l
function c_nullspace(T::Tower{C}, l::Int, elems) where {C}
    r = length(elems)
    all(iszero, elems) && return [C[i == j ? one(C) : zero(C) for i in 1:r] for j in 1:r]
    nullspace_cols(cflat_c(T, l, elems), r)
end

# Σ cᵢ eᵢ for constants cᵢ ∈ C: elements of K_l, and polynomials over the coefficients of level m
function ccomb(T::Tower, l::Int, c, es)
    s = zero(T.Ts[l + 1])
    for (ci, e) in zip(c, es)
        iszero(ci) || (s = s + lconst(T, ci, l) * e)
    end
    s
end
function ccomb_poly(T::Tower, m::Int, c, ps, ::Type{P}) where {P}
    s = zero(P)
    for (ci, p) in zip(c, ps)
        iszero(ci) || (s = s + scale(m == 0 ? ci : lconst(T, ci, m - 1), p))
    end
    s
end
# Σ_j c'ⱼ Nⱼ ∈ C^r: the original parameters from those of a re-parametrisation
function cback(T::Tower{C}, N, cp, r::Int) where {C}
    v = fill(zero(C), r)
    for (j, cj) in enumerate(cp)
        iszero(cj) && continue
        for i in 1:r
            v[i] = v[i] + cj * N[j][i]
        end
    end
    v
end

function prde(T::Tower, m::Int, f, G::Vector; normalized::Bool = false)
    C = ctype(T)
    r = length(G)
    F = T.Ts[m + 1]
    # 0. weak normalisation: y = z/q, z' + (f - Dq/q) z = Σ cᵢ q gᵢ
    if !normalized
        q0 = try
            weak_normalizer(T, m, f)
        catch e
            e isa RischNotImplemented ? nothing : rethrow()
        end
        q0 === nothing && return nothing
        if !isone(q0)
            qF = frac(q0)
            sols = prde(T, m, f - frac(polyD(T, m, q0)) / qF, Any[g * qF for g in G]; normalized = true)
            return sols === nothing ? nothing : [(y / qF, c) for (y, c) in sols]
        end
    end
    lv = m == 0 ? nothing : T.levels[m]
    islog = m == 0 || lv.kind in (:log, :atan)          # the base behaves as t = x primitive over C
    k = coeff_type(T, m)
    P = UPoly{k}
    t = xpoly(k)
    # 1. normal denominator
    dn, _ = split_factor(T, m, f.den)
    en = one(P)
    for g in G
        en = plcm(en, split_factor(T, m, g.den)[1])
    end
    p = gcd(dn, en)
    h = quo(gcd(en, deriv(en)), gcd(p, deriv(p)))
    hF, dnF = frac(h), frac(dn)
    aP = dn * h
    bF = dnF * hF * f - dnF * frac(polyD(T, m, h))
    CF = Any[dnF * hF * hF * g for g in G]
    degree(split_factor(T, m, bF.den)[1]) > 0 && return nothing   # f was not weakly normalised
    # 2. the normal poles left in Σ cᵢ Cᵢ must cancel: Cᵢ = Xᵢ/(d S), constraint Σ cᵢ rem(Xᵢ, d) = 0
    dN, sN = one(P), one(P)
    for c in CF
        nd, sd = split_factor(T, m, c.den)
        dN, sN = plcm(dN, nd), plcm(sN, sd)
    end
    N1 = nothing
    if degree(dN) > 0
        X = [c.num * quo(dN * sN, c.den) for c in CF]
        N1 = c_nullspace(T, m, Any[frac(rem(x, dN)) for x in X])
        Cq = Any[frac(quo(x, dN), sN) for x in X]
        CF = Any[ccomb(T, m, v, Cq) for v in N1]
    end
    # 3. special denominator
    nt = 0
    if islog
        bP, CP = bF.num, P[c.num for c in CF]           # denominators are 1
    else
        wp = liftto(T, D(T, m - 1, lv.arg), m)
        nb = tval(bF)
        nc = minimum((tval(c) for c in CF); init = typemax(Int) ÷ 2)
        lowq = nb < 0 ? nc - nb : min(nc, 0)
        if nb == 0
            b0 = bF.num.c[1 + degree(bF.den)]           # coefficient of t^0 (den = t^v)
            s0 = cancellation_exponent(T, m, b0 / aP.c[1], D(T, m - 1, lv.arg))
            s0 === :unknown && return nothing
            s0 isa Int && (lowq = min(lowq, s0))
        end
        nt = min(0, lowq)
        tn = frac(t)^nt
        b1 = bF + lq(T, Q(nt), m) * wp * frac(aP)
        C1 = Any[c / tn for c in CF]
        Nt = max(0, -tval(b1), maximum((-tval(c) for c in C1); init = 0))
        tN = frac(t^Nt)
        aP = aP * t^Nt
        bP = as_poly(b1 * tN)
        CPs = [as_poly(c * tN) for c in C1]
        (bP === nothing || any(isnothing, CPs)) && throw(RischError("parametric RDE: special denominator not cleared"))
        CP = P[c for c in CPs]
    end
    # 4. degree bound
    n, undecided = rde_degree_bound(T, m, aP, bP, maximum(degree, CP; init = -1))
    undecided && return nothing
    # 5. parametric SPDE, 6. polynomial solutions
    b̄, C̄, M, α, β, N2 = prde_spde(T, m, aP, bP, CP, n)
    hs = prde_poly(T, m, b̄, C̄, M)
    hs === nothing && return nothing
    out = Tuple{F,Vector{C}}[]
    for (hh, c2) in hs
        q = α * hh + ccomb_poly(T, m, c2, β, P)
        c1 = cback(T, N2, c2, length(CP))
        c = N1 === nothing ? c1 : cback(T, N1, c1, r)
        num_, den_ = q, h
        nt >= 0 ? (num_ = num_ * t^nt) : (den_ = den_ * t^(-nt))
        y = frac(num_, den_)
        D(T, m, y) + f * y == ccomb(T, m, c, G) ||
            throw(RischError("parametric RDE solution failed its own check"))
        push!(out, (y, c))
    end
    out
end

# parametric SPDE (Bronstein 7.1): a q' + b q = Σ cᵢ Cᵢ, deg q ≤ n, a, b, Cᵢ ∈ k[t].
# Returns (b̄, C̄, M, α, β, N): for c = Σⱼ c'ⱼ Nⱼ (N a basis of the admissible c),
# q = α h + Σⱼ c'ⱼ βⱼ where h' + b̄ h = Σⱼ c'ⱼ C̄ⱼ and deg h ≤ M (M < 0: h = 0).
function prde_spde(T::Tower, m::Int, a::P, b::P, Cs::Vector, n::Int) where {P<:UPoly}
    C = ctype(T)
    r = length(Cs)
    if n < 0                                            # q = 0: Σ cᵢ Cᵢ = 0
        N = c_nullspace(T, m, Any[frac(c) for c in Cs])
        return (zero(P), P[zero(P) for _ in N], -1, zero(P), P[zero(P) for _ in N], N)
    end
    if degree(a) == 0
        ia = inv(a.c[1])
        ident = [C[i == j ? one(C) : zero(C) for i in 1:r] for j in 1:r]
        return (scale(ia, b), P[scale(ia, c) for c in Cs], n, one(P), P[zero(P) for _ in 1:r], ident)
    end
    g = gcd(a, b)
    if degree(g) > 0                                    # g must divide Σ cᵢ Cᵢ
        qr = [divrem(c, g) for c in Cs]
        N = c_nullspace(T, m, Any[frac(x[2]) for x in qr])
        Cs2 = P[ccomb_poly(T, m, v, [x[1] for x in qr], P) for v in N]
        b̄, C̄, M, α, β, N2 = prde_spde(T, m, quo(a, g), quo(b, g), Cs2, n)
        return (b̄, C̄, M, α, β, [cback(T, N, v, r) for v in N2])
    end
    s, tt, _ = gcdex(b, a)                              # s b + tt a = 1
    rs, zs = P[], P[]
    for c in Cs                                         # b rᵢ + a zᵢ = Cᵢ, deg rᵢ < deg a
        qd, rr = divrem(s * c, a)
        push!(rs, rr)
        push!(zs, tt * c + qd * b)
    end
    b̄, C̄, M, α, β, N = prde_spde(T, m, a, b + polyD(T, m, a),
                                 P[z - polyD(T, m, rr) for (z, rr) in zip(zs, rs)], n - degree(a))
    # q = a h + Σ cᵢ rᵢ with c = Σⱼ c'ⱼ Nⱼ
    βn = P[a * β[j] + ccomb_poly(T, m, N[j], rs, P) for j in eachindex(N)]
    (b̄, C̄, M, a * α, βn, N)
end

# h' + b h = Σ cⱼ Cⱼ in k[t] with deg h ≤ M: a basis [(h, c)] of the solutions, or nothing
function prde_poly(T::Tower, m::Int, b::P, Cs::Vector, M::Int) where {P<:UPoly}
    C = ctype(T)
    r = length(Cs)
    k = coeff_type(T, m)
    zk = zero(k)
    M < 0 && return [(zero(P), v) for v in c_nullspace(T, m, Any[frac(c) for c in Cs])]
    above(p) = frac(P(k[j > M + 1 ? p.c[j] : zk for j in 1:length(p.c)]))   # terms of degree > M
    if degree(b) > 0 || (m == 0 && !iszero(b))          # no cancellation: L(tˢ) has degree s + deg b
        db, lb = degree(b), lc(b)
        hs = P[zero(P) for _ in 1:r]
        res = P[c for c in Cs]
        for s in M:-1:0, i in 1:r
            co = s + db + 1 <= length(res[i].c) ? res[i].c[s + db + 1] : zk
            iszero(co) && continue
            mono = P(k[j == s + 1 ? co / lb : zk for j in 1:(s + 1)])
            hs[i] = hs[i] + mono
            res[i] = res[i] - polyD(T, m, mono) - b * mono
        end
        return [(ccomb_poly(T, m, v, hs, P), v) for v in c_nullspace(T, m, Any[frac(x) for x in res])]
    end
    if m == 0                                           # h' = Σ cⱼ Cⱼ in C[x], plus the constants
        hs = P[integrate_poly(c) for c in Cs]
        out = [(ccomb_poly(T, 0, v, hs, P), v) for v in c_nullspace(T, 0, Any[above(h) for h in hs])]
        push!(out, (one(P), C[zero(C) for _ in 1:r]))
        return out
    end
    # b ∈ k (possibly 0): the coefficients h_s top-down, each from a parametric RDE in k whose
    # right-hand sides are those of the current basis elements
    lv = T.levels[m]
    islog = lv.kind in (:log, :atan)
    b0 = iszero(b) ? zk : b.c[1]
    wp = islog ? zk : D(T, m - 1, lv.arg)
    tp = islog ? lv.dtheta.c[1] : zk
    coef(p, s) = s + 1 <= length(p.c) ? p.c[s + 1] : zk
    # L(h) has degree ≤ M, so the terms of Σ cⱼ Cⱼ above M must cancel
    B = Tuple{P,Vector{C}}[(zero(P), v) for v in c_nullspace(T, m, Any[above(c) for c in Cs])]
    for s in M:-1:0
        rhs = Any[]
        for (hb, cb) in B
            e = zk
            for (ci, Ci) in zip(cb, Cs)
                iszero(ci) || (e = e + lconst(T, ci, m - 1) * coef(Ci, s))
            end
            islog && (e = e - (s + 1) * coef(hb, s + 1) * tp)
            push!(rhs, e)
        end
        sols = prde(T, m - 1, islog ? b0 : b0 + s * wp, rhs)
        sols === nothing && return nothing
        hsB = [x[1] for x in B]
        csB = [x[2] for x in B]
        B = Tuple{P,Vector{C}}[(ccomb_poly(T, m, d, hsB, P) + P(k[j == s + 1 ? y : zk for j in 1:(s + 1)]),
                                cback(T, csB, d, r)) for (y, d) in sols]
    end
    B
end
