# --- real form of a quartic RootSum at a tower level (step RF) ----------------------
# As `quartic_real!`, at level i (θ = θᵢ): residues u ± iv, u′ ± iv′ with u, v ∈ ℚ(√d), d > 0
# (`conj_pair_factors`). W = gcd(D, A - (u + iv) δD) is computed over the tower T3 with constants
# ℚ(i)(√d), split as U = (W + W̄)/2, V = (W - W̄)/(2i) (conjugation i ↦ -i is a field automorphism
# commuting with the derivation, so U, V are fixed by it and read back exactly into T2, the tower
# over ℚ(√d)), and each pair gives u log(U² + V²) + v LogToAtan(U, V) (atans of polynomials in θ).
# The exact derivative is computed in T2 and must lie in T (both pairs together are invariant under
# √d ↦ -√d). `corr` is Σ u·deg_θ(U² + V²), the exp correction.
struct TowerRealForm
    T2::Any
    logs::Vector{Any}        # (c ∈ ℚ(√d), w ∈ T2 at level i)
    atans::Vector{Any}       # (c ∈ ℚ(√d), p ∈ T2 at level i, a polynomial in θ)
    natans::Vector{Any}      # (c, w ∈ ℚ(√d), p ∈ T2 at level i): c √w atan(√w p)  (step NT)
    corr::Q
    deriv::Any               # ∈ Kᵢ of T
end

function tower_quartic_real(T::Tower, i::Int, A::UPoly, Dn::UPoly, dD::UPoly, q::UPoly{Q})
    for (d, q1) in conj_pair_factors(monic(q))
        S = QS{d}
        B3 = QSB{d,QI}
        pairs = Tuple{S,S}[]
        nested = Tuple{S,S}[]                                   # (u, w = v²), v ∉ ℚ(√d) (step NT)
        for qk in (q1, quo(toQS(S, monic(q)), q1))
            u = -qk.c[2] / cfromQ(S, Q(2))
            w = qk.c[1] - u * u
            v = qs_sqrt(w)
            if v === nothing
                real_sign(w) > 0 && push!(nested, (u, w))
                continue
            end
            iszero(v) || push!(pairs, (u, v))
        end
        if length(nested) == 2
            rf = tower_quartic_nested(T, i, A, Dn, dD, S, nested)
            rf === nothing || return rf
            continue
        end
        length(pairs) == 2 || continue
        T2 = change_constants(T, S, c -> cfromQ(S, c))
        φ3(c) = B3(QI(c, Q(0)), zero(QI))
        T3 = change_constants(T, B3, φ3)
        K2, K3 = T2.Ts[i], T3.Ts[i]
        up(p) = UPoly{K3}(K3[change_constants(T, T3, c, φ3) for c in p.c])
        cj(c) = B3(QI(c.a.re, -c.a.im), QI(c.b.re, -c.b.im))
        ψ(c) = (iszero(c.a.im) && iszero(c.b.im)) ? S(c.a.re, c.b.re) : throw(RischError(
            "real form at a tower level: a conjugation-invariant coefficient is not real"))
        half = lconst(T3, B3(QI(Q(1) // 2, Q(0)), zero(QI)), i - 1)
        inv2i = lconst(T3, inv(B3(QI(Q(0), Q(2)), zero(QI))), i - 1)
        logs, atans = Any[], Any[]
        corr = zero(S)
        ok = true
        for (u, v) in pairs
            W = gcd(up(Dn), up(A) - scale(lconst(T3, B3(QI(u.a, v.a), QI(u.b, v.b)), i - 1), up(dD)))
            if degree(W) <= 0
                ok = false
                break
            end
            Uc, Vc = K2[], K2[]
            for w in W.c
                wc = change_constants(T3, T3, w, cj)
                push!(Uc, change_constants(T3, T2, (w + wc) * half, ψ))
                push!(Vc, change_constants(T3, T2, (w - wc) * inv2i, ψ))
            end
            U, V = UPoly{K2}(Uc), UPoly{K2}(Vc)
            if !iszero(u)
                w = U * U + V * V
                push!(logs, (u, frac(w)))
                corr = corr + degree(w) * u
            end
            if !iszero(U) && !iszero(V)
                for p in log_to_atan(U, V)
                    push!(atans, (2 * v, frac(p)))
                end
            end
        end
        ok || continue
        tot = zero(T2.Ts[i + 1])
        for (c, w) in logs
            tot = tot + lconst(T2, c, i) * (D(T2, i, w) / w)
        end
        for (c, p) in atans
            tot = tot + lconst(T2, c, i) * D(T2, i, p) / (one(p) + p * p)
        end
        down(c) = iszero(c.b) ? c.a : throw(RischError("real form at a tower level: derivative not over ℚ"))
        return TowerRealForm(T2, logs, atans, Any[], down(corr), change_constants(T2, T, tot, down))
    end
    nothing
end

# Step NT: NR at a tower level. A conjugate pair u ± i√w (u, w ∈ ℚ(√d), √w ∉ ℚ(√d)): over T2 (the
# tower over ℚ(√d)) W = gcd(D, A − (u + y) δD), y² = −w, by `d5_gcd` with modulus z² + w; W = U + y V′,
# pair = u log(U² + w V′²) + Σ 2√w atan(√w pⱼ) (`log_to_atan_sqrt(U, V′, w)`, pⱼ ∈ K₂[θ]); the
# derivative (c w p′/(1 + w p²) for the atans) is computed in T2 and read back into T.
function tower_quartic_nested(T::Tower, i::Int, A::UPoly, Dn::UPoly, dD::UPoly, ::Type{S}, nested) where {S}
    φ(c) = cfromQ(S, c)
    T2 = change_constants(T, S, φ)
    K2 = T2.Ts[i]
    P2 = UPoly{K2}
    up(p) = P2(K2[map_constants(T, T2, c, φ, i - 1) for c in p.c])
    As, Ds, dDs = up(A), up(Dn), up(dD)
    n = max(length(As.c), length(dDs.c))
    co(p, k) = k <= length(p.c) ? p.c[k] : zero(eltype(p.c))
    logs, natans = Any[], Any[]
    corr = zero(S)
    for (u, w) in nested
        uK, wK = lconst(T2, u, i - 1), lconst(T2, w, i - 1)
        m = P2(K2[wK, zero(K2), one(K2)])                       # z² + w
        a = P2[P2(K2[c]) for c in Ds.c]
        b = P2[P2(K2[co(As, k) - uK * co(dDs, k), -co(dDs, k)]) for k in 1:n]
        outs = d5_gcd(m, a, b)
        length(outs) == 1 || return nothing
        Wv = outs[1][2]
        length(Wv) >= 2 || return nothing
        U = P2(K2[co(c, 1) for c in Wv])
        V = P2(K2[co(c, 2) for c in Wv])
        if !iszero(u)
            ww = U * U + scale(wK, V * V)
            push!(logs, (u, frac(ww)))
            corr = corr + degree(ww) * u
        end
        if !iszero(U) && !iszero(V)
            for p in log_to_atan_sqrt(U, V, wK)
                push!(natans, (cfromQ(S, Q(2)), w, frac(p)))
            end
        end
    end
    tot = zero(T2.Ts[i + 1])
    for (c, ww) in logs
        tot = tot + lconst(T2, c, i) * (D(T2, i, ww) / ww)
    end
    for (c, w, p) in natans
        tot = tot + lconst(T2, c * w, i) * D(T2, i, p) / (one(p) + lconst(T2, w, i) * p * p)
    end
    down(c) = iszero(c.b) ? c.a : throw(RischError("nested real form at a tower level: not over ℚ"))
    TowerRealForm(T2, logs, Any[], natans, down(corr), change_constants(T2, T, tot, down))
end
