# Step R2 (real form of a RootSum). An irreducible quartic residue factor q over ℚ whose roots
# are u ± iv, u′ ± iv′ with u, v, u′, v′ in one real quadratic field ℚ(√d) (then ℚ(α) = ℚ(i, √d)
# and q = q₁·q₂ over ℚ(√d), qₖ = z² - 2uₖ z + uₖ² + vₖ²). The sum s of a conjugate pair is a root of
#   S(t) = Π_{i<j} (t - αᵢ - αⱼ),   S² = res_z(q(z), q(t - z)) / (16 q(t/2)),
# so d is read off a linear or quadratic factor of S over ℚ. Returns candidates (d, q₁), q₁ monic
# quadratic over ℚ(√d) dividing q (not yet checked for complex roots).
function conj_pair_factors(q::CX)
    c = q.c
    K = CXF
    lin = UPoly{K}(K[frac(xpoly(Q)), kconst(Q(-1))])            # t - z, as a polynomial in z
    qtz = foldr((ci, acc) -> acc * lin + UPoly{K}(K[kconst(ci)]), c; init = zero(UPoly{K}))
    r = resultant(UPoly{K}(K[kconst(ci) for ci in c]), qtz)
    out = Any[]
    isone(r.den) || return out
    S2, r0 = divrem(r.num, CX(Q[16 * c[k] / Q(2)^(k - 1) for k in eachindex(c)]))
    iszero(r0) || return out
    for g in factor_Q(quo(S2, gcd(S2, deriv(S2))))
        degree(g) <= 2 || continue
        # the quadratic whose roots are in ℚ(√d): for a linear g (s rational) both pairs have sum
        # s, so q = (z² - sz + p₁)(z² - sz + p₂) and p₁, p₂ are the roots of y² - P y + Pr
        if degree(g) == 1
            s = -g.c[1]
            c[4] == -2s || continue
            P, Pr = c[3] - s^2, c[1]
            e0, e1 = Pr, -P                                     # y² + e1 y + e0
        else
            e0, e1 = g.c[1], g.c[2]
        end
        Δ = e1^2 - 4 * e0
        Δ > 0 || continue
        sd, d = sqfree_split(numerator(Δ) * denominator(Δ))
        (d == 1 || d > 10^9) && continue
        S = QS{Int(d)}
        root = S(-e1 / 2, Q(sd) / (2 * denominator(Δ)))         # (-e1 + √Δ)/2
        qS = toQS(S, q)
        if degree(g) == 1
            q1 = UPoly{S}(S[root, cfromQ(S, -s), one(S)])
        else                                                    # q₁ = gcd(q(z), q(s - z))
            l = UPoly{S}(S[root, -one(S)])
            q1 = gcd(qS, foldr((ci, acc) -> acc * l + UPoly{S}(S[ci]), qS.c; init = zero(UPoly{S})))
        end
        degree(q1) == 2 && iszero(rem(qS, q1)) && push!(out, (Int(d), q1))
    end
    out
end

# log and atan terms over ℚ(√d) for an irreducible quartic residue factor q (see above); false if
# its roots are not of that kind (q then stays a RootSum). Each conjugate pair u ± iv gives, as in
# `quad_factor!`, with W = gcd(D, A - (u + iv) D') = U + iV, U, V ∈ ℚ(√d)[x]:
#   u log(U² + V²) + v LogToAtan(U, V)  (atans of polynomials).
# The terms of both pairs (σ-conjugate, σ: √d ↦ -√d) are returned together as one
# RationalIntegral over ℚ(√d) in `quads`: only their sum has a derivative in ℚ(x).
function quartic_real!(quads, A::CX, D::CX, dD::CX, q::CX)
    for (d, q1) in conj_pair_factors(monic(q))
        S = QS{d}
        B2 = QSB{d,QI}
        qS = toQS(S, monic(q))
        pairs = Tuple{S,S}[]
        nested = Tuple{S,S}[]                                   # (u, w = v²) with v ∉ ℚ(√d) (step NR)
        for qk in (q1, quo(qS, q1))
            u = -qk.c[2] / cfromQ(S, Q(2))
            w = qk.c[1] - u * u
            v = qs_sqrt(w)                                      # a square in ℚ(√d), d > 0: v² > 0
            if v === nothing
                real_sign(w) > 0 && push!(nested, (u, w))       # complex roots u ± i√w, √w nested
                continue
            end
            iszero(v) || push!(pairs, (u, v))
        end
        if length(nested) == 2
            push!(quads, quartic_nested(A, D, dD, S, nested))
            return true
        end
        length(pairs) == 2 || continue
        toB2(p::CX) = UPoly{B2}(B2[B2(QI(a, Q(0)), zero(QI)) for a in p.c])
        logs = Tuple{S,UPoly{S}}[]
        atans = Tuple{S,Frac{UPoly{S}}}[]
        for (u, v) in pairs
            α = B2(QI(u.a, v.a), QI(u.b, v.b))
            W = gcd(toB2(D), toB2(A) - scale(α, toB2(dD)))
            U = UPoly{S}(S[S(w.a.re, w.b.re) for w in W.c])
            V = UPoly{S}(S[S(w.a.im, w.b.im) for w in W.c])
            iszero(u) || push!(logs, (u, U * U + V * V))
            if !iszero(U) && !iszero(V)
                for p in log_to_atan(U, V)
                    push!(atans, (2 * v, frac(p)))
                end
            end
        end
        push!(quads, RationalIntegral(zero(Frac{UPoly{S}}), logs, atans, Any[]))
        return true
    end
    false
end

# Step NR: nested radicals. A conjugate pair u ± iv with u, w = v² ∈ ℚ(√d) but v = √w ∉ ℚ(√d)
# (e.g. the residues of 1/(x⁵+1): Im ζ₁₀ = √(10 − 2√5)/4). W = gcd(D, A − (u + y) D') with y² = −w is
# computed by `d5_gcd` over ℚ(√d) with modulus z² + w (irreducible: −w < 0), W = U + y V′, so with
# y = i√w: W = U + iV, V = √w V′, and the pair gives u log(U² + w V′²) + √w·LogToAtan(U, √w V′) =
# u log(U² + w V′²) + Σ 2√w atan(√w uⱼ) (`log_to_atan_sqrt`, uⱼ over ℚ(√d)). Stored as
# `QuarticNested`: logs (c, w) and nested atans (c, w, u) = c √w atan(√w u), whose derivative
# c w u'/(1 + w u²) lies in ℚ(√d)(x); both pairs together come down to ℚ(x) (`qs_down`).
struct QuarticNested{S}
    logs::Vector{Tuple{S,UPoly{S}}}
    natans::Vector{Tuple{S,S,UPoly{S}}}
end
function quartic_nested(A::CX, D::CX, dD::CX, ::Type{S}, nested) where {S}
    P = UPoly{S}
    toS(p) = P(S[cfromQ(S, c) for c in p.c])
    As, Ds, dDs = toS(A), toS(D), toS(dD)
    n = max(length(As.c), length(dDs.c))
    co(p, k) = k <= length(p.c) ? p.c[k] : zero(S)
    logs = Tuple{S,P}[]
    natans = Tuple{S,S,P}[]
    for (u, w) in nested
        m = P(S[w, zero(S), one(S)])                            # z² + w, z = y
        a = P[P(S[c]) for c in Ds.c]
        b = P[P(S[co(As, k) - u * co(dDs, k), -co(dDs, k)]) for k in 1:n]   # A − (u + z) D'
        outs = d5_gcd(m, a, b)
        length(outs) == 1 || throw(RischNotImplemented("nested real form: the modulus z² + w split"))
        Wv = outs[1][2]
        U = P(S[co(c, 1) for c in Wv])
        V = P(S[co(c, 2) for c in Wv])
        iszero(u) || push!(logs, (u, U * U + scale(w, V * V)))
        if !iszero(U) && !iszero(V)
            for p in log_to_atan_sqrt(U, V, w)
                push!(natans, (cfromQ(S, Q(2)), w, p))
            end
        end
    end
    QuarticNested{S}(logs, natans)
end
function derivative_of(q::QuarticNested{S}) where {S}
    F = Frac{UPoly{S}}
    tot = zero(F)
    for (c, w) in q.logs
        tot = tot + kconst(c) * frac(deriv(w), w)
    end
    for (c, w, u) in q.natans                                   # (c √w atan(√w u))' = c w u'/(1 + w u²)
        tot = tot + kconst(c * w) * frac(deriv(u), one(UPoly{S}) + scale(w, u * u))
    end
    tot
end
function to_term(b, q::QuarticNested)              # b: a Builder (defined below)
    ts = Any[]
    for (c, w) in q.logs
        l = mk(b, :log, poly_term(b, w))
        push!(ts, isone(c) ? l : mk(b, :*, cterm(b, c), l))
    end
    for (c, w, u) in q.natans
        r = mk(b, :sqrt, cterm(b, w))
        l = mk(b, :atan, mk(b, :*, r, poly_term(b, u)))
        push!(ts, isone(c) ? mk(b, :*, r, l) : mk(b, :*, cterm(b, c), r, l))
    end
    isempty(ts) ? b.lift(0) : length(ts) == 1 ? ts[1] : mk(b, :+, ts...)
end
