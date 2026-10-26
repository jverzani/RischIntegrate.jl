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

# Step BQ4: an irreducible even quartic G = x⁴ + b x² + c over ℚ with b² < 4c whose residues need nested radicals
# (1/(x⁴ + 2x² + 2): ±√((1 ± i)/32)). G = (x² + r x + q)(x² - r x + q), q = √c, r = √(2q - b), s = √(2q + b)
# (both real: |b| < 2q). For A = a₀ + a₁x + a₂x² + a₃x³:
#   odd part, y = x²:  ∫ (a₁x + a₃x³)/G = (a₃/4) log G + (a₁ - a₃b/2)/√e atan((2x² + b)/√e),  e = 4c - b²
#   even part, a₀ + a₂x² = α(x² + q) + β(x² - q):
#     ∫ (x² + q)/G = (1/s) (atan((2x + r)/s) + atan((2x - r)/s)),
#     ∫ (x² - q)/G = (1/(2r)) log((x² - r x + q)/(x² + r x + q)),
# all continuous on ℝ. The term keeps its derivative A/G (Rubi's form, with √(√2 ± 1) for 1/(x⁸ + 4)).
struct BiquadTerm
    A::QX
    G::QX
end
derivative_of(q::BiquadTerm) = frac(q.A, q.G)
tower_quad(q::BiquadTerm) = BaseTerms(q, derivative_of(q))
is_biquad(g::QX) = degree(g) == 4 && iszero(g.c[2]) && iszero(g.c[4]) && isone(g.c[5]) && g.c[1] > 0 &&
                   g.c[3]^2 < 4 * g.c[1]

# A/D (D squarefree, monic) with the even quartic factors of D split off as `BiquadTerm`s, the rest by `log_part`;
# nothing when D has none
function biquad_log_part(A::QX, D::QX)
    gs = filter(is_biquad, factor_Q(D))
    isempty(gs) && return nothing
    logs, atans, unresolved, quads = Tuple{Q,QX}[], Tuple{Q,Frac{QX}}[], Any[], Any[]
    for G in gs
        H = quo(D, G)
        s, t, g = gcdex(H, G)                           # s H + t G = 1
        isone(g) || return nothing
        push!(quads, BiquadTerm(rem(A * s, G), G))
        A, D = rem(A * t, H), H
    end
    if degree(D) > 0 && !iszero(A)
        l2, a2, u2, q2 = log_part(A, D)
        append!(logs, l2); append!(atans, a2); append!(unresolved, u2); append!(quads, q2)
    end
    logs, atans, unresolved, quads
end

function to_term(b, q::BiquadTerm)
    co(p, k) = k <= length(p.c) ? p.c[k] : Q(0)
    a0, a1, a2, a3 = co(q.A, 1), co(q.A, 2), co(q.A, 3), co(q.A, 4)
    bb, c = q.G.c[3], q.G.c[1]
    x = b.x
    rt(v::Q) = (s = rat_sqrt(v); s === nothing ? mk(b, :sqrt, cterm(b, v)) : cterm(b, s))
    sc(c, t) = isone(c) ? t : mk(b, :*, c isa Q ? cterm(b, c) : c, t)
    x2 = mk(b, :^, x, b.lift(2))
    ts = Any[]
    iszero(a3) || push!(ts, sc(a3 / 4, mk(b, :log, poly_term(b, q.G))))
    k = a1 - a3 * bb / 2
    if !iszero(k)
        e = 4c - bb^2
        se = rt(e)
        arg = mk(b, :/, poly_term(b, QX(Q[bb, 0, 2])), se)
        push!(ts, mk(b, :*, mk(b, :/, cterm(b, k), se), mk(b, :atan, arg)))
    end
    if !iszero(a0) || !iszero(a2)
        sq = rat_sqrt(c)
        qt = rt(c)
        # (2q ∓ b) under the square roots, as terms
        two_q = sq === nothing ? mk(b, :*, b.lift(2), qt) : cterm(b, 2sq)
        rarg = sq === nothing ? mk(b, :+, two_q, cterm(b, -bb)) : cterm(b, 2sq - bb)
        sarg = sq === nothing ? mk(b, :+, two_q, cterm(b, bb)) : cterm(b, 2sq + bb)
        r = sq !== nothing && rat_sqrt(2sq - bb) !== nothing ? cterm(b, rat_sqrt(2sq - bb)) : mk(b, :sqrt, rarg)
        s = sq !== nothing && rat_sqrt(2sq + bb) !== nothing ? cterm(b, rat_sqrt(2sq + bb)) : mk(b, :sqrt, sarg)
        # α, β = a₂/2 ± a₀/(2q)
        a0q = iszero(a0) ? nothing : mk(b, :/, cterm(b, a0 / 2), qt)
        α = a0q === nothing ? cterm(b, a2 / 2) : iszero(a2) ? a0q : mk(b, :+, cterm(b, a2 / 2), a0q)
        β = a0q === nothing ? cterm(b, a2 / 2) :
            iszero(a2) ? mk(b, :*, b.lift(-1), a0q) : mk(b, :+, cterm(b, a2 / 2), mk(b, :*, b.lift(-1), a0q))
        rx = mk(b, :*, r, x)
        twox = mk(b, :*, b.lift(2), x)
        at1 = mk(b, :atan, mk(b, :/, mk(b, :+, twox, r), s))
        at2 = mk(b, :atan, mk(b, :/, mk(b, :+, twox, mk(b, :*, b.lift(-1), r)), s))
        push!(ts, mk(b, :*, mk(b, :/, α, s), mk(b, :+, at1, at2)))
        lq = mk(b, :log, mk(b, :/, mk(b, :+, x2, mk(b, :*, b.lift(-1), rx), qt), mk(b, :+, x2, rx, qt)))
        push!(ts, mk(b, :*, mk(b, :/, β, mk(b, :*, b.lift(2), r)), lq))
    end
    isempty(ts) ? b.lift(0) : length(ts) == 1 ? ts[1] : mk(b, :+, ts...)
end

# the x-jump at ±∞ of the two linear atans (bioche), as a term, or nothing
function biquad_jump(b, q::BiquadTerm)
    co(p, k) = k <= length(p.c) ? p.c[k] : Q(0)
    a0, a2 = co(q.A, 1), co(q.A, 3)
    (iszero(a0) && iszero(a2)) && return nothing
    t = to_term(b, BiquadTerm(QX(Q[a0, 0, a2]), q.G))       # (only the even part has linear atans)
    nothing === t && return nothing
    c, bb = q.G.c[1], q.G.c[3]
    sq = rat_sqrt(c)
    qt = sq === nothing ? mk(b, :sqrt, cterm(b, c)) : cterm(b, sq)
    sarg = sq === nothing ? mk(b, :+, mk(b, :*, b.lift(2), qt), cterm(b, bb)) : cterm(b, 2sq + bb)
    s = mk(b, :sqrt, sarg)
    a0q = iszero(a0) ? nothing : mk(b, :/, cterm(b, a0 / 2), qt)
    α = a0q === nothing ? cterm(b, a2 / 2) : iszero(a2) ? a0q : mk(b, :+, cterm(b, a2 / 2), a0q)
    mk(b, :/, mk(b, :*, b.lift(2), α), s)                   # 2 atans, coefficient α/s, σ = +1 each
end
