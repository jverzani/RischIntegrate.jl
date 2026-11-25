# ---------------------------------------------------------------------------
# Step PX: ∫ P(x) R(θ), θ = e^(u), u = η x + u₀ (η ∈ C, written trig and hyperbolic functions of a linear argument
# included), when the residues of the remainder are polynomials in x (not constants): ∫ x/(a + b sin x),
# ∫ (c + d x)² sech(a + b x), ∫ x² eˣ/(a + b e²ˣ). After Hermite reduction in θ the remainder R/D has simple poles at
# the roots r ≠ 0 of D ∈ C[θ], with residues a_r(x) = R(x, r)/D′(r) polynomial in x. With z = θ/r, z′ = η z and
# Li₀(z) = z/(1 - z), Li′ₙ(z) = η Li_{n-1}(z):
#   a/(θ - r) = -(1/r)(a z/(1 - z) + a),   ∫ w Li₀(z) = Σ_{j≥0} (-1)ʲ w⁽ʲ⁾ Li_{j+1}(z)/η^(j+1)  (w polynomial in x),
# so ∫ R/D = Σ_r Σ_j (-1)ʲ w_r⁽ʲ⁾ Li_{j+1}(θ/r)/η^(j+1) + ∫ R(0)/D(0), w_r = -a_r/r, and Σ_r -a_r/r = (R/D)(0) stays
# in the field (it joins the θ⁰ part). Linear factors of D: r ∈ C. Other factors q (split by factor_Q, or by step ST
# over parameters): w and 1/r computed in K[θ]/(q) as Σ wₖθᵏ, Σ ρₖθᵏ, printed at the roots of q: q = θ² + pθ + s,
# r = -p/2 ± √(p²/4 - s) (x/(a + b sin x)); q = θ⁴ + pθ² + s, r = ±√y, y = -p/2 ± √(p²/4 - s) (x/(a + b sin²x)).
# Other degrees: refused. The answer is in complex form, as Rubi writes it (Li_{j+1} of e^(i(c + d x))/r with i); its derivative is
# the integrand exactly (the term's derivative R/D - (R/D)(0) is checked with the rest of the tower). Only after
# steps CL, XP decline (their answers are real), with PX_ACTIVE: one exp level over C(x).
# ---------------------------------------------------------------------------
struct ExpPolylogTerm
    η::Any                 # θ′ = η θ, η ∈ C
    roots::Vector{Any}     # (:lin, r ∈ C, w ∈ K) or (:alg, q ∈ C[θ], [wₖ] ∈ K, [ρₖ] ∈ C): w, 1/r mod q
    deriv::Any             # R/D - (R/D)(0), at level 1
end

const MAX_PX_DEGREE = 8    # deg_x of the residues

function exp_polylog(T::Tower, i::Int, R::UPoly, Dsf::UPoly)
    PX_ACTIVE[] || return nothing
    (i == 1 && length(T.levels) == 1 && T.levels[1].kind === :exp) || return nothing
    degree(R) < degree(Dsf) || return nothing
    C = ctype(T)
    K = T.Ts[1]
    P = UPoly{K}
    η = dconst_value(T, D(T, 0, T.levels[1].arg))
    (η === nothing || iszero(η)) && return nothing
    l = lc(Dsf)
    R, Dsf = scale(inv(l), R), scale(inv(l), Dsf)
    Dc = C[]
    for c in Dsf.c
        v = dconst_value(T, c)
        v === nothing && return nothing
        push!(Dc, v)
    end
    iszero(Dc[1]) && return nothing
    DC = UPoly{C}(Dc)
    rest = DC
    lins = C[]
    for r in constant_roots(DC)
        lin = UPoly{C}(C[-r, one(C)])
        iszero(rem(rest, lin)) || continue
        push!(lins, r)
        rest = quo(rest, lin)
    end
    qs = px_factors(T, monic(rest))
    qs === nothing && return nothing
    lk(c) = lconst(T, c, 0)
    polyx(w) = degree(w.den) == 0 && degree(w.num) <= MAX_PX_DEGREE
    dD = deriv(Dsf)
    roots = Any[]
    for r in lins
        rk = lk(r)
        w = -(peval(R, rk) / peval(dD, rk)) / rk
        polyx(w) || return nothing
        push!(roots, (:lin, r, w))
    end
    # each factor q: w = -a/r and ρ = 1/r in K[θ]/(q) (q squarefree, not necessarily irreducible: the values at
    # every root of q)
    θ = xpoly(K)
    for qc in qs
        q = P(K[lk(c) for c in qc.c])
        s1, _, g1 = gcdex(rem(dD, q), q)                # s₁ D′ ≡ g₁ (mod q)
        s2, _, g2 = gcdex(rem(θ, q), q)                 # s₂ θ ≡ g₂
        (degree(g1) == 0 && degree(g2) == 0) || return nothing
        a = scale(inv(g1.c[1]), rem(R * s1, q))
        ρ = scale(inv(g2.c[1]), s2)
        w = rem(-(a * ρ), q)
        n = degree(qc)
        ws = K[k <= length(w.c) ? w.c[k] : zero(K) for k in 1:n]
        all(polyx, ws) || return nothing
        ρs = Any[dconst_value(T, k <= length(ρ.c) ? ρ.c[k] : zero(K)) for k in 1:n]
        any(isnothing, ρs) && return nothing
        push!(roots, (:alg, qc, ws, C[c for c in ρs]))
    end
    isempty(roots) && return nothing
    extra = peval(R, zero(K)) / peval(Dsf, zero(K))
    d = frac(R, Dsf) - frac(P(K[extra]))
    ExpPolylogTerm(η, roots, d), extra
end

# the factors of rest ∈ C[θ] (monic, no roots in C) whose roots can be written: degree 2, or degree 4 in θ² only.
# Split by factor_Q over ℚ, by the factor free of the outermost parameter (step ST) over ℚ(t₁, …); nothing if a
# factor of another kind is left
function px_factors(T::Tower, rest::UPoly{C}) where {C}
    degree(rest) == 0 && return UPoly{C}[]
    ok(q) = degree(q) == 2 || (degree(q) == 4 && iszero(q.c[2]) && iszero(q.c[4]))
    ok(rest) && return [rest]
    if C === Q
        fs = factor_Q(rest)
        out = UPoly{C}[]
        for f in fs                                     # (two quadratics in θ² only: their product)
            ok(f) || return nothing
            push!(out, f)
        end
        return out
    end
    rational_tfield(C) || return nothing
    K = T.Ts[1]
    G = tower_tfree_factor(T, 1, UPoly{K}(K[lconst(T, c, 0) for c in rest.c]))
    G === nothing && return nothing
    gc = Any[dconst_value(T, c) for c in G.c]
    any(isnothing, gc) && return nothing
    Gc = monic(UPoly{C}(C[c for c in gc]))
    H, r = divrem(rest, Gc)
    iszero(r) || return nothing
    a, b = px_factors(T, Gc), px_factors(T, monic(H))
    (a === nothing || b === nothing) ? nothing : vcat(a, b)
end

# the term: Σ_r Σ_j (-1)ʲ w_r⁽ʲ⁾ Li_{j+1}(θ/r)/η^(j+1), Li₁(z) = -log(1 - z)
function exp_polylog_out(b::Builder, T::Tower, q::ExpPolylogTerm)
    C = typeof(q.η)
    θt = theta_term(b, T, 1)
    ts = Any[]
    for rt in q.roots, (Ws, ρt) in px_root_terms(b, T, rt)
        z = mk(b, :*, ρt, θt)
        for (j, Wt) in enumerate(Ws)
            Wt === nothing && continue
            c = (iseven(j) ? -one(C) : one(C)) / q.η^j
            Wc = isone(c) ? Wt : isone(-c) ? mk(b, :*, b.lift(-1), Wt) : mk(b, :*, cterm(b, c), Wt)
            push!(ts, mk(b, :*, Wc, px_li(b, j, z)))
        end
    end
    isempty(ts) ? b.lift(0) : length(ts) == 1 ? ts[1] : mk(b, :+, ts...)
end

px_li(b::Builder, n::Int, z) = n == 1 ? mk(b, :*, b.lift(-1), mk(b, :log, mk(b, :+, b.lift(1), mk(b, :*, b.lift(-1), z)))) :
                               mk(b, :polylog, b.lift(n), z)
# w, w′, w″, … up to the last nonzero (w a polynomial in x)
function px_derivs(T::Tower, w)
    ws = Any[w]
    while !iszero(ws[end]) && length(ws) <= MAX_PX_DEGREE + 1
        push!(ws, D(T, 0, ws[end]))
    end
    ws[1:end-1]
end
# terms with `nothing` for zero
px_add(b::Builder, s, t) = s === nothing ? t : t === nothing ? s : mk(b, :+, s, t)
px_mul(b::Builder, s, t) = (s === nothing || t === nothing) ? nothing : mk(b, :*, s, t)
# Σ cₖ rᵏ with r² = y: c₀ + c₁ r (degree 2), (c₀ + c₂ y) + r (c₁ + c₃ y) (degree 4 in θ²)
px_at(b::Builder, cs, r, y) = length(cs) == 2 ? px_add(b, cs[1], px_mul(b, cs[2], r)) :
    px_add(b, px_add(b, cs[1], px_mul(b, cs[3], y)), px_mul(b, r, px_add(b, cs[2], px_mul(b, cs[4], y))))

# for each root r of the factor: ([w⁽ʲ⁾(r) for j = 0, 1, …] as terms, 1/r as a term)
function px_root_terms(b::Builder, T::Tower, rt)
    xt(w) = tower_to_term(b, T, w)
    if rt[1] === :lin
        _, r, w = rt
        return [(Any[xt(v) for v in px_derivs(T, w)], cterm(b, inv(r)))]
    end
    _, qc, ws, ρs = rt
    C = eltype(qc.c)
    half = inv(cfromQ(C, Q(2)))
    even = degree(qc) == 4
    p, s = even ? (qc.c[3], qc.c[1]) : (qc.c[2], qc.c[1])
    sqt = px_sqrt(b, p * p * half * half - s)
    dws = [px_derivs(T, w) for w in ws]
    nj = maximum(length, dws; init = 0)
    ct(c) = iszero(c) ? nothing : cterm(b, c)
    out = Any[]
    for σ in (1, -1)
        v = px_add(b, iszero(p) ? nothing : cterm(b, -p * half), σ == 1 ? sqt : mk(b, :*, b.lift(-1), sqt))
        rs = even ? (mk(b, :sqrt, v), mk(b, :*, b.lift(-1), mk(b, :sqrt, v))) : (v,)
        for r in rs
            Ws = Any[px_at(b, Any[j <= length(d) ? xt(d[j]) : nothing for d in dws], r, v) for j in 1:nj]
            push!(out, (Ws, px_at(b, Any[ct(c) for c in ρs], r, v)))
        end
    end
    out
end

# step PX: the tower of f, one exp level over C(x), integrated with the polylog residues allowed; nothing unless
# that gives an answer
function try_exp_polylog(f, x; build = nothing, lift = nothing, verify::Bool = true)
    @nospecialize f x
    # (not inside step AT's u = tan t: there step AP's real answer by parts follows, ∫ atan(x)/(x + c) with Li₂)
    (PX_ACTIVE[] || ATAN_SUBST[]) && return nothing
    xk = string(x)
    T, el = try
        build_tower(f, xk)
    catch e
        (e isa RischNotImplemented || e isa RischError || e isa NotElementary) && return nothing
        rethrow()
    end
    (length(T.levels) == 1 && T.levels[1].kind === :exp && levelof(T, el) == 1) || return nothing
    bd = Builder(build === nothing ? auto_build(f, x) : build, lift === nothing ? auto_lift(f, x) : lift, x, T.consts)
    PX_ACTIVE[] = true
    try
        integrate_built(T, el, bd, verify)
    catch e
        (e isa NotElementary || e isa RischNotImplemented) || rethrow()
        nothing
    finally
        PX_ACTIVE[] = false
    end
end

# √δ as a term: in C when it is a square there, i √(-δ) for a negative rational δ, else sqrt(δ)
function px_sqrt(b::Builder, δ)
    sq = csqrt(δ)
    sq === nothing || return cterm(b, sq)
    δq = crational(δ)
    if δq !== nothing && δq < 0
        rq = rat_sqrt(-δq)
        return rq === nothing ? mk(b, :*, b.lift(im), mk(b, :sqrt, cterm(b, -δq))) :
               isone(rq) ? b.lift(im) : mk(b, :*, cterm(b, rq), b.lift(im))
    end
    mk(b, :sqrt, cterm(b, δ))
end
