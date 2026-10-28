# ---------------------------------------------------------------------------
# Stage 3: integration in a monomial extension  K(θ),  K = Kᵢ₋₁
#
#   ∫ f = v + Σ cⱼ log(wⱼ) (+ Σ dⱼ atan(uⱼ) at the base level),  v, wⱼ ∈ Kᵢ, cⱼ ∈ ℚ
#        (+ quadratic-irrational pairs √d·log(…) / √e·atan(…) at any level, Stage 5b)
#
# 1. exp only: split off the special part θ^m of the denominator (Laurent terms).
# 2. Hermite reduction (generic, uses the tower derivation) -> rational part g.
# 3. Residue criterion (Bronstein Thm 5.6.1): R(z) = res_θ(D, A - z·δD) ∈ K[z]
#    must have constant roots, else the integral is not elementary.
#    Log part Σ c log gcd(D, A - c δD); for exp, ∫ v'/v has an extra term
#    -deg(v)·u (since δv/v = deg(v)·u' + proper fraction).
# 4. Polynomial part. log: top-down reduction with limited integration of the
#    leading coefficient (Bronstein 5.8). exp: the θʲ terms need the Risch
#    differential equation y' + j u' y = aⱼ  (Stage 4); only j = 0 is done here.
# ---------------------------------------------------------------------------
struct ElemIntegral{C}
    v::Any                              # rational part, element of Kᵢ
    logs::Vector{Tuple{C,Any}}          # (c, w):  c * log(w),  c ∈ C
    atans::Vector{Tuple{C,Any}}         # (c, u):  c * atan(u), u ∈ C(x) (base level only)
    quads::Vector{Any}                  # TowerQuadLog / TowerQuadAtan (C = ℚ only)
end
ElemIntegral(v, logs, atans) = ElemIntegral(v, logs, atans, Any[])

# Stage 5b: a pair of conjugate quadratic-irrational residues a, ā = α ± β√d (d squarefree)
# of a residue polynomial over ℚ, at any level of the tower. With W = gcd(D, A - a·δD) computed
# over ℚ(√d) (via `change_constants`) and split as W = U + √d V with U, V ∈ Kᵢ₋₁[θ]:
#   a log W + ā log W̄ = α log(U² - d V²) + β√d log((U + √d V)/(U - √d V))       (d > 1)
#                      = α log(U² + e V²) + β√e LogToAtan(U, √e V),  e = -d     (d < 0)
# The α-part is an ordinary log term; the other part is one of these (U, V, u tower elements):
struct TowerQuadLog             # β√d · log((U + √d V)/(U - √d V)),  d > 1
    β::Q
    d::Int
    U::Any
    V::Any
    sq::Bool                    # printed as (β√d/2) log(ratio²) (steps EC, TL)
end
TowerQuadLog(β, d, U, V) = TowerQuadLog(β, d, U, V, false)
struct TowerQuadAtan            # c√e · atan(√e u)  (inverted = false)  or  c√e · atan(u/√e)  (true)
    c::Q
    e::Int
    u::Any
    inverted::Bool
end

# Step 7: a conjugate pair of residues a, σ_d(a) = α ± β√d (α, β ∈ ℚ(i), d > 1 squarefree) of a
# residue polynomial over ℚ(i):  a log W + σ_d(a) log σ_d(W),  kept over the tower T2 = T with
# constants ℚ(i)(√d) (σ_d: √d ↦ -√d fixes ℚ(i)). Its derivative is σ_d-invariant, i.e. in T.
struct ExtQuadPair
    T2::Any
    a::Any                 # ∈ ℚ(i)(√d)
    W::Any                 # monic in θ, element of T2 at the level it was found
end
galois_d(c::QSB{d,B}) where {d,B} = QSB{d,B}(c.a, -c.b)
qs_down(c::QSB) = iszero(c.b) ? c.a :
    throw(RischError("a constant of ℚ(i)(√d) that should lie in ℚ(i) does not"))
ext_corr(q::ExtQuadPair) = qs_down(q.a + galois_d(q.a)) * degree(q.W.num)   # 2α·deg W

# Δ = s² d with s ∈ ℚ(i) and d > 1 a squarefree integer, or nothing. If Δ = s² d, s = u + vi,
# then u² = (p + |Δ|)/(2d) and v² = (|Δ| - p)/(2d), so d is the squarefree part of 2(p ± |Δ|)
# (a negative part is absorbed into s: √(-d) = i√d).
function qi_split_sqrt(Δ::QI)
    p, q = Δ.re, Δ.im
    m = rat_sqrt(p^2 + q^2)
    m === nothing && return nothing
    for cand in (2 * (p + m), 2 * (p - m))
        iszero(cand) && continue
        _, d0 = sqfree_split(numerator(cand) * denominator(cand))
        d = abs(d0)
        (d == 1 || d > 10^9) && continue
        s = qi_sqrt(Δ / QI(Q(d), Q(0)))
        s === nothing || return Int(d), s
    end
    nothing
end

# the pair of roots of the quadratic `rest` ∈ ℚ(i)[z] as an ExtQuadPair (and its exp correction
# 2α·deg W), or nothing if the roots are not of the form α ± β√d
function ext_quad_terms(T::Tower, i::Int, A::UPoly, D::UPoly, dD::UPoly, rest::UPoly{QI})
    rest = monic(rest)
    p0, p1 = rest.c[1], rest.c[2]
    sp = qi_split_sqrt(p1 * p1 - 4 * p0)
    sp === nothing && return nothing
    dd, s = sp
    half = inv(QI(Q(2), Q(0)))
    α, β = -p1 * half, s * half
    S = QSB{dd,QI}
    φ(c) = S(c, zero(QI))
    T2 = change_constants(T, S, φ)
    K2 = T2.Ts[i]
    up(p) = UPoly{K2}(K2[change_constants(T, T2, c, φ) for c in p.c])
    a = S(α, β)
    W = gcd(up(D), up(A) - scale(lconst(T2, a, i - 1), up(dD)))
    degree(W) > 0 || return nothing
    ExtQuadPair(T2, a, frac(W))
end

# the Stage 5a terms of a rational integral, as tower terms (U, V, u ∈ K₀ = ℚ(x))
tower_quad(q::QuadLog) = TowerQuadLog(q.β, q.d, frac(q.U), frac(q.V), q.sq)
tower_quad(q::QuadAtan) = TowerQuadAtan(q.c, q.e, q.u, q.inverted)

# Step T1: the real form of a quartic RootSum (R2), a RationalIntegral over ℚ(√d) in x only, as a
# tower term: its derivative is in K₀ = ℚ(x) (stored, for `check_tower`), output by `to_term`.
# It has no θ, so it adds nothing to the exp correction Σ c·deg W.
struct BaseTerms
    q::Any                   # RationalIntegral over ℚ(√d) (R2) or QuarticNested (NR)
    deriv::Any
end
tower_quad(q::RationalIntegral) = BaseTerms(q, qs_down(derivative_of(q)))
tower_quad(q::QuarticNested) = BaseTerms(q, qs_down(derivative_of(q)))

# The conjugate pair of roots of the irreducible quadratic `rest` ∈ ℚ[z] as log/atan terms
# (see above), or nothing if this case is not handled. A, D, dD = δD ∈ Kᵢ₋₁[θᵢ].
function tower_quad_terms(T::Tower, i::Int, A::UPoly, D::UPoly, dD::UPoly, rest::UPoly{Q})
    rest = monic(rest)
    p0, p1 = rest.c[1], rest.c[2]
    α = -p1 / 2
    Δ = p1^2 - 4 * p0
    iszero(Δ) && return nothing
    s, d = sqfree_split(numerator(Δ) * denominator(Δ))
    (d == 1 || abs(d) > 10^9) && return nothing
    β = Q(s) / (2 * denominator(Δ))                  # roots α ± β√d
    dd = Int(d)
    S = QS{dd}
    φ(c) = cfromQ(S, c)                               # ℚ -> ℚ(√d)
    σ(c) = S(c.a, -c.b)                               # √d -> -√d
    ψ(c) = iszero(c.b) ? c.a : throw(RischError(      # back to ℚ, on σ-invariant elements
        "splitting a quadratic-residue gcd: a σ-invariant coefficient is not rational"))
    T2 = change_constants(T, S, φ)
    K, K2 = T.Ts[i], T2.Ts[i]
    up(p) = UPoly{K2}(K2[change_constants(T, T2, c, φ) for c in p.c])
    # φ commutes with the derivation, so the image of δD is δ′ of the image of D
    W = gcd(up(D), up(A) - scale(lconst(T2, S(α, β), i - 1), up(dD)))
    degree(W) > 0 || return nothing
    # W = U + √d V:  U = (W + σW)/2,  V = (W - σW)/(2√d). Both are σ-invariant, and a σ-invariant
    # element in normalised form has σ-invariant base coefficients (the normal form is unique and
    # σ preserves it), so ψ reads them back exactly.
    half = lq(T2, Q(1) // 2, i - 1)
    inv2r = lconst(T2, inv(S(Q(0), Q(2))), i - 1)
    Uc, Vc = K[], K[]
    for w in W.c
        wσ = change_constants(T2, T2, w, σ)
        push!(Uc, change_constants(T2, T, (w + wσ) * half, ψ))
        push!(Vc, change_constants(T2, T, (w - wσ) * inv2r, ψ))
    end
    U, V = UPoly{K}(Uc), UPoly{K}(Vc)
    logs = Tuple{Q,Any}[]
    quads = Any[]
    iszero(α) || push!(logs, (α, U * U - dd * (V * V)))
    if !iszero(V)
        Uf, Vf = frac(U), frac(V)
        if dd > 0
            push!(quads, TowerQuadLog(β, dd, Uf, Vf))
        elseif !iszero(U)                            # β√e LogToAtan(U, √e V) (step T2)
            e = -dd
            for u in log_to_atan_sqrt(U, V, lq(T, Q(e), i - 1))
                push!(quads, TowerQuadAtan(2 * β, e, frac(u), false))
            end
        end
    end
    logs, quads
end

# R(z) = res_θ(D, A - z·dD) ∈ K[z] (formal degree of A - z·dD: n = max(deg A, deg dD)) by evaluation
# and interpolation: deg R ≤ deg D, so R is fixed by its values at deg D + 1 points z = 0, 1, 2, …
# (j·1 in K), each a resultant over K alone; Euclid over K(z) instead normalises nested
# fractions at every step and is far slower when K is itself ℚ(i)(e)(x)…. A point where A - z·dD
# drops below degree n is skipped (the evaluated resultant then differs from R(z_j)).
# Over K = B(t₁, …, tₖ), K a rational function field, a constant multiple of R (callers need only its roots):
# D, A, dD scaled into the ring B[t₁, …, tₖ] once, fraction-free resultants there (step FR) and no
# division by the scale factors, whose gcds over K would cost more than the resultants.
function residue_resultant(D::UPoly{K}, A::UPoly{K}, dD::UPoly{K}) where {K<:Frac}
    m, n = integral_multiplier(K, D.c), integral_multiplier(K, [A.c; dD.c])
    sc(p, c) = UPoly{K}(K[a * c for a in p.c])
    residue_resultant(sc(D, m), sc(A, n), sc(dD, n), ff_resultant)
end
function residue_resultant(D::UPoly{K}, A::UPoly{K}, dD::UPoly{K}, res = resultant) where {K}
    n = max(length(A.c), length(dD.c))
    ai(k) = k <= length(A.c) ? A.c[k] : zero(K)
    di(k) = k <= length(dD.c) ? dD.c[k] : zero(K)
    zs, vs = K[], K[]
    j = 0
    while length(zs) <= degree(D)
        z = j * one(K)
        j += 1
        B = UPoly{K}(K[ai(k) - z * di(k) for k in 1:n])
        length(B.c) == n || continue
        push!(zs, z)
        push!(vs, res(D, B))
    end
    interpolate(zs, vs)
end

# the polynomial over K through the points (zs[k], vs[k]) (Newton divided differences)
function interpolate(zs::Vector{K}, vs::Vector{K}) where {K}
    c = copy(vs)
    for l in 2:length(zs), m in length(zs):-1:l
        c[m] = (c[m] - c[m - 1]) / (zs[m] - zs[m - l + 1])
    end
    R = UPoly{K}(K[c[end]])
    for m in (length(zs) - 1):-1:1
        R = R * UPoly{K}(K[-zs[m], one(K)]) + UPoly{K}(K[c[m]])
    end
    R
end

# R(z) = res_θ(D, A - z δD) must have constant roots. Returns (logs, quads): logs are
# [(c, W)] with W = gcd(D, A - c δD) ∈ Kᵢ₋₁[θ] (also the α log(U² - dV²) terms of a quadratic
# pair: for the exp correction Σ c·deg W they count exactly like the two conjugate logs), and
# quads the TowerQuadLog / TowerQuadAtan terms of irreducible quadratic residue factors.
# Step ST (SD inside towers). The factor of D ∈ K[θ] free of the outermost constant generator t
# (C = B(t)): specialise t to two rationals (a ring map on the constants, only used to find a
# candidate), take G = gcd of the two images of D, lift it back (its constants lie in B) and accept
# it only if it divides D exactly. Returns G (monic) or nothing.
inner_field(::Type{Frac{UPoly{B}}}) where {B} = B
function tower_tfree_factor(T::Tower{C}, i::Int, D::UPoly) where {C}
    rational_tfield(C) || return nothing
    B = inner_field(C)
    cands = Any[]
    for t in (2, 3, 5, 7, 11, 13)
        length(cands) == 2 && break
        bt = cfromQ(B, Q(t))
        φ(c) = (d = peval(c.den, bt); iszero(d) ? throw(DomainError(t)) : peval(c.num, bt) / d)
        try
            Tt = change_constants(T, B, φ)
            Kt = Tt.Ts[i]
            Dt = UPoly{Kt}(Kt[map_constants(T, Tt, c, φ, i - 1) for c in D.c])
            degree(Dt) == degree(D) && push!(cands, (Tt, Dt))
        catch e
            e isa InterruptException && rethrow()     # a bad specialisation point: try the next one
        end
    end
    length(cands) == 2 || return nothing
    G = gcd(cands[1][2], cands[2][2])
    (0 < degree(G) < degree(D)) || return nothing
    K = T.Ts[i]
    GL = UPoly{K}(K[map_constants(cands[1][1], T, c, kconst, i - 1) for c in G.c])
    iszero(rem(D, GL)) ? monic(GL) : nothing
end

function residue_logs(T::Tower, i::Int, A::UPoly, D::UPoly)
    if rational_tfield(ctype(T)) && !iszero(A)
        G = tower_tfree_factor(T, i, D)
        if G !== nothing                       # A/D = A₁/G + A₂/H, residues separately (step ST)
            H, r = divrem(D, G)
            iszero(r) || throw(RischError("tower_tfree_factor: G does not divide D"))
            sH, uG, g = gcdex(H, G)
            isone(g) || throw(RischError("tower_tfree_factor: G and D/G are not coprime"))
            o1, q1 = residue_logs(T, i, rem(A * sH, G), G)
            o2, q2 = residue_logs(T, i, rem(A * uG, H), H)
            return vcat(o1, o2), vcat(q1, q2)
        end
    end
    K = T.Ts[i]
    dD = Dp(T, i, D)
    CT0 = ctype(T)
    CT0 <: Frac && cdepth(CT0) > MAX_ROOTSUM_GENS && degree(D) > 2 && throw(RischNotImplemented(
        "residues of a denominator of degree $(degree(D)) over more than $MAX_ROOTSUM_GENS symbolic constants"))
    Rz = residue_resultant(D, A, dD)
    iszero(Rz) && throw(RischError("zero resultant in the residue computation"))
    CT = ctype(T)
    out = Tuple{CT,Any}[]
    quads = Any[]
    degree(Rz) <= 0 && return out, quads
    Rm = monic(Rz)
    qc = CT[]
    for c in Rm.c
        v = dconst_value(T, c)
        v === nothing && throw(NotElementary(
            "the residues of the integrand are not constants (residue criterion)"))
        push!(qc, v)
    end
    Rq = UPoly{CT}(qc)
    Rsf = quo(Rq, gcd(Rq, deriv(Rq)))
    rest = Rsf
    for a in constant_roots(Rsf)
        W = gcd(D, A - scale(lconst(T, a, i - 1), dD))
        degree(W) > 0 && push!(out, (a, W))
        rest = quo(rest, UPoly{CT}(CT[-a, one(CT)]))
    end
    if CT === Q && degree(rest) >= 2
        hard = one(rest)
        for q in (degree(rest) > 2 ? factor_Q(rest) : [rest])
            if degree(q) == 2                          # a conjugate pair in ℚ(√d) (Stage 5b)
                qt = tower_quad_terms(T, i, A, D, dD, q)
                if qt !== nothing
                    append!(out, qt[1])
                    append!(quads, qt[2])
                    continue
                end
            end
            if degree(q) == 4                          # real form with √d (step RF)
                rf = tower_quartic_real(T, i, A, D, dD, q)
                if rf !== nothing
                    push!(quads, rf)
                    continue
                end
            end
            hard = hard * q
        end
        degree(hard) > 0 && append!(quads, tower_root_sums(T, i, A, D, dD, hard))   # step RT
        rest = one(rest)
    elseif CT === QI && degree(rest) >= 2
        if degree(rest) == 2                           # a pair α ± β√d over ℚ(i) (Step 7)
            qt = ext_quad_terms(T, i, A, D, dD, rest)
            if qt !== nothing
                push!(quads, qt)
                rest = one(rest)
            end
        end
        if degree(rest) > 0                            # RootSum over ℚ(i) (step RC; no factoring)
            append!(quads, tower_root_sums(T, i, A, D, dD, rest))
            rest = one(rest)
        end
    elseif rational_tfield(CT) && degree(rest) > 0          # RootSum over ℚ(t₁, …) (step RE; no factoring)
        append!(quads, tower_root_sums(T, i, A, D, dD, rest))
        rest = one(rest)
    end
    degree(rest) > 0 && throw(RischNotImplemented(
        "the residues are algebraic constants of degree ≥ 2 over the constant field $CT " *
        "(RootSum inside towers is implemented over ℚ and ℚ(i) only)"))
    out, quads
end

# log(w) as an element of K_j (w ∈ K_j) up to a constant, when w'/w is a ℚ-combination of the log
# generators' and exp arguments' derivatives with a constant ratio (as in `make_log`, without adding a
# level); else nothing
function log_element(T::Tower, j::Int, w)
    j == 0 && return nothing
    w = liftto(T, w, j)
    K = T.Ts[j + 1]
    idx = [l for l in 1:j if T.levels[l].kind in (:exp, :log)]
    isempty(idx) && return nothing
    basis = K[T.levels[l].kind === :exp ? liftto(T, D(T, l - 1, T.levels[l].arg), j) :
                                          liftto(T, T.levels[l].dtheta.c[1], j) for l in idx]
    r = solve_relation(T, D(T, j, w) / w, basis)
    r === nothing && return nothing
    q = reduce(lcm, denominator.(r); init = big(1))
    R = w^Int(q)
    res = zero(K)
    for (ri, l) in enumerate(idx)
        ρ = r[ri]
        iszero(ρ) && continue
        lv = T.levels[l]
        e = Int(numerator(ρ * q))
        if lv.kind === :exp
            R = R / liftto(T, theta(T, l), j)^e
            res = res + lq(T, ρ, j) * liftto(T, lv.arg, j)
        else
            R = R / liftto(T, lv.arg, j)^e
            res = res + lq(T, ρ, j) * liftto(T, theta(T, l), j)
        end
    end
    dconst_value(T, R) === nothing ? nothing : res
end

# ∫ p, p ∈ K[θ], θ = log(u): returns (q ∈ K[θ], logs (c, w ∈ K), atans, quads) with
# Dq + Σ c w'/w (+ atan and quadratic terms, which only come from the constant term) = p
function integrate_log_poly(T::Tower, i::Int, p::UPoly)
    K = T.Ts[i]
    P = UPoly{K}
    Lθ = T.levels[i].dtheta.c[1]                       # u'/u (atan level: u'/(1 + u²))
    isatan = T.levels[i].kind === :atan
    q = zero(P)
    while degree(p) > 0
        n = degree(p)
        r = integrate_el(T, i - 1, lc(p))
        # Limited integration (step 9d): lc(p) = b' + c u'/u with b ∈ K, c ∈ C is required. An atan,
        # quadratic-irrational or ExtQuadPair term carries residues outside C, which b' (residues 0)
        # and c u'/u (residues in C) cannot produce; a SpecialTerm means ∫ lc(p) is not elementary.
        # At an atan level (step TA) the atan terms are what c θ' is made of, so they join the target.
        ((isatan || isempty(r.atans)) && isempty(r.quads)) || throw(NotElementary(
            "the integral of the coefficient of log^$n needs logarithms with residues outside the constant field"))
        tgt = zero(K)                                   # Σ cⱼ wⱼ'/wⱼ, must equal c·u'/u
        rv = r.v
        for (cj, wj) in r.logs
            le = isatan ? log_element(T, i - 1, wj) : nothing   # log w already in the tower (TA)
            if le !== nothing
                rv = rv + lconst(T, cj, i - 1) * le
            else
                tgt = tgt + lconst(T, cj, i - 1) * (D(T, i - 1, wj) / wj)
            end
        end
        for (cj, uj) in r.atans                         # only at an atan level (base atans: uj ∈ K₀)
            du = liftto(T, dx(uj) / (one(uj) + uj * uj), i - 1)
            tgt = tgt + lconst(T, cj, i - 1) * du
        end
        # ∫ lc(p) = r.v + c·log(u) with c a constant of the field (c ∈ C, not only ℚ:
        # e.g. ∫ e·log(x)/x needs c = e). Lθ = u'/u ≠ 0, so c = tgt/Lθ, and it must be constant.
        c = zero(ctype(T))
        if !iszero(tgt)
            cv = dconst_value(T, tgt / Lθ)
            if cv === nothing                           # tgt - c·u'/u may still be a derivative b' with b ∈ K
                cb = log_ratio_match(T, i - 1, tgt, Lθ)  # (log(e²ˣ + 1) - x = log(cosh x) + log 2)
                cb === nothing && throw(NotElementary(
                    "the integral of the coefficient of log^$n involves logarithms other than log(u)"))
                cv, bv = cb
                rv = rv + bv
            end
            c = cv
        end
        coeffs = fill(zero(K), n + 2)
        coeffs[n + 2] = lconst(T, c / cfromQ(ctype(T), Q(n + 1)), i - 1)
        coeffs[n + 1] = rv
        qn = P(coeffs)
        q = q + qn
        p = p - Dp(T, i, qn)
        degree(p) < n || throw(RischError("polynomial reduction did not lower the degree"))
    end
    logs = Tuple{ctype(T),Any}[]
    atans = Tuple{ctype(T),Any}[]
    quads = Any[]
    if !iszero(p)
        r0 = integrate_el(T, i - 1, p.c[1])
        q = q + P(K[r0.v])
        append!(logs, r0.logs)
        append!(atans, r0.atans)
        append!(quads, r0.quads)
    end
    q, logs, atans, quads
end

# c ∈ C and b ∈ K with tgt = c·L + b' (tgt, L log derivatives in K = Kⱼ), or nothing: the candidates for
# c are the ratios of the log coefficients of ∫ tgt and ∫ L; c is right when ∫ (tgt - c L) has no logs
function log_ratio_match(T::Tower, j::Int, tgt, L)
    rt, rl = integrate_el(T, j, tgt), integrate_el(T, j, L)
    (isempty(rt.atans) && isempty(rt.quads) && isempty(rl.atans) && isempty(rl.quads)) || return nothing
    for (ct, _) in rt.logs, (cl, _) in rl.logs
        c = ct / cl
        rr = try
            integrate_el(T, j, tgt - lconst(T, c, j) * L)
        catch e
            (e isa NotElementary || e isa RischNotImplemented) || rethrow()
            continue
        end
        (isempty(rr.logs) && isempty(rr.atans) && isempty(rr.quads)) && return (c, rr.v)
    end
    nothing
end

function integrate_el(T::Tower, i::Int, f)::ElemIntegral
    if i == 0
        res = integrate_rational(f)
        isempty(res.unresolved) || ctype(T) === Q || ctype(T) === QI || rational_tfield(ctype(T)) || throw(RischNotImplemented(
            "the logarithmic part has residues of degree > 2 over the constant field $(ctype(T))"))
        quads = Any[tower_quad(q) for q in res.quads]
        for (rest, R, Dd) in res.unresolved, rs in root_sums(rest, R, Dd, "x")    # step RT
            push!(quads, BaseRootSum(rs, rootsum_derivative(rs)))
        end
        return ElemIntegral(res.rational,
                            Tuple{ctype(T),Any}[(c, frac(w)) for (c, w) in res.logs],
                            Tuple{ctype(T),Any}[(c, u) for (c, u) in res.atans], quads)
    end
    lv = T.levels[i]
    K = T.Ts[i]
    P = UPoly{K}
    F = T.Ts[i + 1]
    iszero(f) && return ElemIntegral(zero(F), Tuple{ctype(T),Any}[], Tuple{ctype(T),Any}[])
    δ(p) = Dp(T, i, p)
    A, Dn = f.num, f.den
    laurent = Dict{Int,K}()
    addl!(j::Int, α) = (laurent[j] = get(laurent, j, zero(K)) + α)
    θ = xpoly(K)
    if lv.kind === :exp
        m = findfirst(c -> !iszero(c), Dn.c) - 1        # multiplicity of θ in D
        if m > 0
            N = quo(Dn, θ^m)
            s, t, g1 = gcdex(θ^m, N)
            isone(g1) || throw(RischError("special part: gcd(θ^m, N) != 1"))
            At = A * t                                  # f = A t/θ^m + A s/N
            for (k, α) in enumerate(At.c)
                addl!(k - 1 - m, α)
            end
            A, Dn = A * s, N
        end
    end
    g, Qp, R, Dsf = hermite_reduce(δ, A, Dn)
    for (k, α) in enumerate(Qp.c)
        addl!(k - 1, α)
    end
    logs = Tuple{ctype(T),Any}[]
    atans = Tuple{ctype(T),Any}[]
    quads = Any[]
    corr = zero(ctype(T))
    if !iszero(R)
        rl, rq = try
            residue_logs(T, i, R, Dsf)
        catch e
            (e isa NotElementary && lv.kind === :log) || rethrow()
            sp = special_log(T, i, R, Dsf)
            if sp === nothing                               # one factor θ + b of several: split it off
                sps = special_log_split(T, i, R, Dsf)
                sps === nothing && rethrow()
                sps
            else
                Tuple{ctype(T),Any}[], Any[sp]             # li-type: c·e^p·Ei(k·log(u) + k·b) (Step 8a)
            end
        end
        for (c, W) in rl
            push!(logs, (c, frac(W)))
            corr += c * degree(W)
        end
        for q in rq                                     # 5b ratio terms: degree 0, no correction
            q isa ExtQuadPair && (corr += ext_corr(q))
            q isa TowerRootSum && (corr += rootsum_corr(q))
            q isa TowerRealForm && (corr += q.corr)
        end
        append!(quads, rq)
    end
    v = g
    if lv.kind in (:log, :atan)                         # primitive levels (atan: step TA)
        maxj = maximum(keys(laurent); init = 0)
        p = P(K[get(laurent, j, zero(K)) for j in 0:maxj])
        q, lp, ap, qp = try
            integrate_log_poly(T, i, p)
        catch e
            # step DL: θ log(a x + b) · (simple rational poles) is a dilogarithm
            e isa NotElementary || rethrow()
            dl = dilog_split(T, i, p)
            dl === nothing && rethrow()
            p, dterms, qextra = dl
            r = try
                integrate_log_poly(T, i, p)
            catch e2
                e2 isa NotElementary ? rethrow(e) : rethrow()
            end
            (r[1] + qextra, r[2], r[3], vcat(r[4], dterms))
        end
        v = v + frac(q)
        for (c, w) in lp
            push!(logs, (c, frac(P(K[w]))))
        end
        append!(atans, ap)
        append!(quads, qp)
    else
        for (j, α) in laurent                           # ∫ α θ^j = y θ^j  with  y' + j u' y = α
            (j == 0 || iszero(α)) && continue
            fj = lq(T, Q(j), i - 1) * D(T, i - 1, lv.arg)
            y = rde(T, i - 1, fj, α)
            if y === nothing                            # not elementary; try Ei / erf (Step 8a)
                sp = special_exp(T, i, j, α)
                sp === nothing && throw(NotElementary(
                    "the Risch differential equation y' + $j·u'·y = a has no solution in the coefficient field, " *
                    "so the coefficient of exp(u)^$j has no elementary integral"))
                y = sp[1]
                append!(quads, sp[2])
            end
            if j > 0
                coeffs = fill(zero(K), j + 1)
                coeffs[j + 1] = y
                v = v + frac(P(coeffs))
            else
                v = v + frac(P(K[y]), θ^(-j))
            end
        end
        a0 = get(laurent, 0, zero(K))
        if !iszero(a0)
            r0 = integrate_el(T, i - 1, a0)
            v = v + frac(P(K[r0.v]))
            for (c, w) in r0.logs
                push!(logs, (c, frac(P(K[w]))))
            end
            append!(atans, r0.atans)
            append!(quads, r0.quads)
        end
        iszero(corr) || (v = v - lconst(T, corr, i) * liftto(T, lv.arg, i))
    end
    ElemIntegral(v, logs, atans, quads)
end

# d/dx of the antiderivative, computed in the tower, must equal the integrand
function check_tower(T::Tower, L::Int, res::ElemIntegral, f)
    tot = D(T, L, liftto(T, res.v, L))
    for (c, w) in res.logs
        w = liftto(T, w, L)
        tot = tot + lconst(T, c, L) * (D(T, L, w) / w)
    end
    for (c, u) in res.atans
        du = liftto(T, dx(u) / (one(T.Ts[1]) + u * u), L)
        tot = tot + lconst(T, c, L) * du
    end
    for q in res.quads
        if q isa TowerQuadLog   # d/dx [β√d log((U+√dV)/(U-√dV))] = 2βd (V'U - U'V)/(U² - dV²)
            U, V = liftto(T, q.U, L), liftto(T, q.V, L)
            num_ = D(T, L, V) * U - D(T, L, U) * V
            tot = tot + lq(T, 2 * q.β * q.d, L) * num_ / (U * U - lq(T, Q(q.d), L) * (V * V))
        elseif q isa TowerQuadAtan  # c√e atan(√e u): c e u'/(1 + e u²);  c√e atan(u/√e): c e u'/(e + u²)
            u, e = liftto(T, q.u, L), lq(T, Q(q.e), L)
            den = q.inverted ? e + u * u : one(u) + e * u * u
            tot = tot + lq(T, q.c * q.e, L) * D(T, L, u) / den
        elseif q isa SpecialTerm || q isa BaseTerms || q isa TowerRootSum || q isa BaseRootSum ||
               q isa TowerRealForm || q isa DilogTerm || q isa DilogPairTerm || q isa DilogQuadTerm || q isa DilogGroup ||
               q isa DilogConjTerm
            # stored exact derivatives (8a, T1, RT, RF)
            tot = tot + liftto(T, q.deriv, L)
        elseif q isa ExtQuadPair    # a W'/W + σ_d(a W'/W), computed over ℚ(i)(√d), read back in T
            T2 = q.T2
            w = liftto(T2, q.W, L)
            t1 = lconst(T2, q.a, L) * (D(T2, L, w) / w)
            t2 = change_constants(T2, T2, t1, galois_d)
            tot = tot + change_constants(T2, T, t1 + t2, qs_down)
        else
            throw(RischError("unknown term $(typeof(q))"))
        end
    end
    tot == f
end

function to_term(b::Builder, T::Tower, res::ElemIntegral)
    ts = Any[]
    iszero(res.v) || push!(ts, tower_to_term(b, T, res.v))
    for (c, w) in res.logs
        l = mk(b, :log, levelof(T, w) == 0 ? log_arg_term(b, w) : tower_to_term(b, T, w))
        push!(ts, isone(c) ? l : mk(b, :*, cterm(b, c), l))
    end
    for (c, u) in res.atans
        l = mk(b, :atan, frac_term(b, u))
        push!(ts, isone(c) ? l : mk(b, :*, cterm(b, c), l))
    end
    shc, used = shi_chi_terms(b, T, res.quads)          # Ei(w), Ei(-w) pairs as Shi, Chi (H4)
    append!(ts, shc)
    for (qi, q) in enumerate(res.quads)
        qi in used && continue
        if q isa TowerQuadLog
            r = mk(b, :sqrt, b.lift(q.d))
            Ut, Vt = tower_to_term(b, T, q.U), tower_to_term(b, T, q.V)
            top = mk(b, :+, Ut, mk(b, :*, r, Vt))
            bot = mk(b, :+, Ut, mk(b, :*, b.lift(-1), r, Vt))
            ratio = mk(b, :/, top, bot)
            l = mk(b, :log, q.sq ? mk(b, :^, ratio, b.lift(2)) : ratio)
            β = q.sq ? q.β / 2 : q.β
            push!(ts, isone(β) ? mk(b, :*, r, l) : mk(b, :*, cterm(b, β), r, l))
        elseif q isa SpecialTerm
            push!(ts, special_out(b, q, cterm(b, q.c), z -> tower_to_term(b, T, z)))
        elseif q isa BaseTerms
            push!(ts, to_term(b, q.q))
        elseif q isa DilogTerm
            push!(ts, dilog_term(b, q))
        elseif q isa DilogPairTerm
            push!(ts, dilog_pair_term(b, q))
        elseif q isa DilogQuadTerm
            push!(ts, dilog_quad_term(b, q))
        elseif q isa DilogConjTerm
            push!(ts, dilog_conj_term(b, q))
        elseif q isa DilogGroup
            push!(ts, dilog_group_term(b, q))
        elseif q isa TowerRealForm
            for (c, w) in q.logs
                l = mk(b, :log, tower_to_term(b, q.T2, w))
                push!(ts, isone(c) ? l : mk(b, :*, cterm(b, c), l))
            end
            for (c, p) in q.atans
                l = mk(b, :atan, tower_to_term(b, q.T2, p))
                push!(ts, isone(c) ? l : mk(b, :*, cterm(b, c), l))
            end
            for (c, w, p) in q.natans                   # c √w atan(√w p)  (step NT)
                r = mk(b, :sqrt, cterm(b, w))
                l = mk(b, :atan, mk(b, :*, r, tower_to_term(b, q.T2, p)))
                push!(ts, isone(c) ? mk(b, :*, r, l) : mk(b, :*, cterm(b, c), r, l))
            end
        elseif q.e == 1                              # residues ±i: c·atan(u), no sqrt(1)
            l = mk(b, :atan, tower_to_term(b, T, q.u))
            push!(ts, isone(q.c) ? l : mk(b, :*, cterm(b, q.c), l))
        else
            r = mk(b, :sqrt, b.lift(q.e))
            ut = tower_to_term(b, T, q.u)
            l = mk(b, :atan, q.inverted ? mk(b, :/, ut, r) : mk(b, :*, r, ut))
            push!(ts, isone(q.c) ? mk(b, :*, r, l) : mk(b, :*, cterm(b, q.c), r, l))
        end
    end
    isempty(ts) && return b.lift(0)
    length(ts) == 1 ? ts[1] : mk(b, :+, ts...)
end
