# --- exp and log of tower elements --------------------------------------------
# Structure theorem (Risch): exp(u) is not new iff  u' = Σ ρᵢ bᵢ'  with ρ ∈ ℚ, where bᵢ is the
# argument of an exp level and θᵢ of a log level; then  u = Σ ρᵢ bᵢ + c  with c a constant
# (D c = 0), and  exp(u) = exp(c) Π θᵢ^ρᵢ (exp levels) Π argᵢ^ρᵢ (log levels). exp(c) is
# found in the constant field (`const_exp`), which may ask for a new constant generator.
function make_exp(T::Tower, u)
    c = dconst_value(T, u)
    if c !== nothing
        iszero(c) && return one(T.Ts[1])
        return lconst(T, const_exp(T, c), 0)
    end
    top = length(T.levels)
    u = liftto(T, u, top)
    K = T.Ts[end]
    basis = K[]
    idx = [i for (i, lv) in enumerate(T.levels) if lv.kind !== :atan]   # exp(ρ atan) is new (step TA)
    for i in idx
        lv = T.levels[i]
        push!(basis, lv.kind === :exp ? liftto(T, lv.arg, top) : liftto(T, theta(T, i), top))
    end
    dbasis = K[D(T, top, b) for b in basis]
    r = solve_relation(T, D(T, top, u), dbasis)
    if r !== nothing
        off = u
        for (ρ, b) in zip(r, basis)
            iszero(ρ) || (off = off - lq(T, ρ, top) * b)
        end
        cv = dconst_value(T, off)
        cv === nothing && throw(RischError("inconsistent exponential relation (offset not constant)"))
        res = iszero(cv) ? one(K) : lconst(T, const_exp(T, cv), top)
        for (ri, i) in enumerate(idx)
            lv = T.levels[i]
            ρ = r[ri]
            iszero(ρ) && continue
            if lv.kind === :exp
                denominator(ρ) == 1 || throw(Restart(lv.seq, Int(denominator(ρ))))
                res = res * liftto(T, theta(T, i), top)^Int(numerator(ρ))
            else
                denominator(ρ) == 1 || throw(RischNotImplemented(
                    "exp of a rational multiple of a logarithm is an algebraic (radical) function"))
                res = res * liftto(T, lv.arg, top)^Int(numerator(ρ))
            end
        end
        return res
    end
    seq = (T.nexp += 1)
    s = get(T.scales, seq, 1)
    arg = s == 1 ? u : u * lq(T, Q(1) // s, top)
    add_level!(T, :exp, arg, UPoly{K}(K[zero(K), D(T, top, arg)]), seq)
    th = theta(T, top + 1)
    s == 1 ? th : th^s
end

# the times make_log identified log(-w) with log(w), dropping the constant iπ (counted for the power parse)
const NEG_LOG_DROPPED = Ref(0)
function make_log(T::Tower, u)
    c = dconst_value(T, u)
    if c !== nothing
        isone(c) && return zero(T.Ts[1])
        return lconst(T, const_log(T, c), 0)
    end
    top = length(T.levels)
    u = liftto(T, u, top)
    K = T.Ts[end]
    w = D(T, top, u) / u
    basis = K[]
    idx = [i for (i, lv) in enumerate(T.levels) if lv.kind !== :atan]   # atan' is no log-derivative (TA)
    for i in idx
        lv = T.levels[i]
        push!(basis, lv.kind === :exp ? liftto(T, D(T, i - 1, lv.arg), top) :
                                        liftto(T, lv.dtheta.c[1], top))
    end
    r = solve_relation(T, w, basis)
    if r !== nothing
        # u^q = c * prod(...)  with c a constant; log u = sum r_i * (log of generator i) + log c / q
        q = reduce(lcm, denominator.(r); init = big(1))
        R = u^Int(q)
        res = zero(T.Ts[1])
        for (ri, i) in enumerate(idx)
            lv = T.levels[i]
            ρ = r[ri]
            iszero(ρ) && continue
            e = Int(numerator(ρ * q))
            if lv.kind === :exp
                R = R / liftto(T, theta(T, i), top)^e
                res = liftto(T, res, top) + lq(T, ρ, top) * liftto(T, lv.arg, top)
            else
                R = R / liftto(T, lv.arg, top)^e
                res = liftto(T, res, top) + lq(T, ρ, top) * liftto(T, theta(T, i), top)
            end
        end
        cv = dconst_value(T, R)
        cv === nothing && throw(RischError("inconsistent logarithmic relation (not a constant ratio)"))
        res = liftto(T, res, top)
        # u^q = cv · Π(...): log u = Σ ρᵢ (log of generator i) + log(cv)/q. A ratio of -1 keeps the
        # behaviour from before Step 6 (the constant log(-1) = iπ is dropped).
        if !(isone(cv) || isone(-cv))
            res = res + lconst(T, const_log(T, cv) / cfromQ(ctype(T), Q(q)), top)
        end
        isone(-cv) && (NEG_LOG_DROPPED[] += 1)        # (a power uᵏ, k ∉ ℤ, then refuses: e^(iπk) is lost)
        return res
    end
    add_level!(T, :log, u, UPoly{K}(K[w]), 0)
    theta(T, top + 1)
end

# Step TA: atan(u), a primitive monomial: θ' = u'/(1 + u²) ∈ K. It is new unless θ' is a ℚ-linear
# combination of x' = 1, the exp arguments' derivatives and the log/atan generators' derivatives;
# such a relation holds only up to an unknown (possibly piecewise) constant — atan(tan x) = x,
# atan(1/x) = π/2 - atan(x) — so it is refused rather than guessed. atan of a nonzero constant
# (π/4, …) needs π, which no constant field here contains.
function make_atan(T::Tower, u)
    c = dconst_value(T, u)
    if c !== nothing
        iszero(c) && return zero(T.Ts[1])
        throw(RischNotImplemented("atan of a nonzero constant (it would need π)"))
    end
    top = length(T.levels)
    u = liftto(T, u, top)
    K = T.Ts[end]
    w = D(T, top, u) / (one(u) + u * u)
    basis = K[liftto(T, one(T.Ts[1]), top)]
    for (i, lv) in enumerate(T.levels)
        push!(basis, lv.kind === :exp ? liftto(T, D(T, i - 1, lv.arg), top) : liftto(T, lv.dtheta.c[1], top))
    end
    solve_relation(T, w, basis) === nothing || throw(RischNotImplemented(
        "an atan depends on the other generators (equal to them up to an undetermined constant, " *
        "e.g. atan(1/x) = π/2 - atan(x))"))
    add_level!(T, :atan, u, UPoly{K}(K[w]), 0)
    theta(T, top + 1)
end
