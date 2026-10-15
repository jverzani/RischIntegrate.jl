# ---------------------------------------------------------------------------
# Public API
# ---------------------------------------------------------------------------
"""
    risch_integrate(f, x; build = nothing, lift = nothing, verify = true)

The antiderivative of the term `f` in the variable `x` (the function behind [`integrate`](@ref)).
`build` and `lift` control how the answer is built as a term; `verify = false` skips the final
check of the answer by differentiation (every answer is checked by default). Returns a term, or an
[`IntegralWithRootSums`](@ref); throws [`NotElementary`](@ref) or [`RischNotImplemented`](@ref).
"""
function risch_integrate(f, x; build = nothing, lift = nothing, verify::Bool = true)
    check_leaves(f, string(x))                                         # step WR
    try
        integrate_direct(f, x; build = build, lift = lift, verify = verify)
    catch e
        (e isa RischNotImplemented || e isa NotElementary) || rethrow()
        r = try_usub(f, x; build = build, lift = lift, verify = verify)    # step US
        r === nothing && throw(e)
        r
    end
end

function integrate_direct(f, x; build = nothing, lift = nothing, verify::Bool = true)
    xk = string(x)
    # step IT: a factor free of x containing other symbols comes out, ∫ c g dx = c ∫ g dx (keeps the
    # parameter out of the constant field, and lets an iterated integral see c(y)·RootSum(x))
    cg = split_free_factor(f, x, xk, build, lift)
    if cg !== nothing
        c, g, bd = cg
        G = risch_integrate(g, x; build = build, lift = lift, verify = verify)
        G isa IntegralWithRootSums && return IntegralWithRootSums(mk(bd, :*, c, G.elementary),
                                                                 Any[ScaledRootSum(c, rs) for rs in G.rootsums], G.var)
        return mk(bd, :*, c, G)
    end
    has_op(f, :acot) && return risch_integrate(rewrite_acot(f, x, build, lift), x; build = build, lift = lift,
                                               verify = verify)     # acot(u) = atan(1/u) (step AC)
    arcs = collect_arcs(f, xk)                  # asin / acos: substitution u = sin t / cos t (step AS)
    isempty(arcs) || return integrate_arcsin(f, x, arcs; build = build, lift = lift, verify = verify)
    rads = collect_radicals(f, xk)
    if !isempty(rads)
        # only powers of √(1 - u²), u linear: the substitution u = sin t first (gives asin(u)), step AS
        a1 = unit_circle_radicand(f, x, rads, xk; build = build, lift = lift)
        if a1 !== nothing
            try
                return integrate_arcsin(f, x, a1[1]; sK = a1[2], radicand = a1[3], build = build, lift = lift,
                                        verify = verify)
            catch e
                e isa RischNotImplemented || rethrow()
            end
        end
    end
    if !isempty(rads)                  # a RootSum is in the substitution variable t: evaluate through x
        F = integrate_radical(f, x, rads; build = build, lift = lift, verify = verify)
        return F isa IntegralWithRootSums ? IntegralWithRootSums(F.elementary, F.rootsums, xk) : F
    end
    if has_trig(f)                     # polynomial × exp × trig first (Stage 5c), else the ℚ(i) tower
        try
            return integrate_trig(f, x; build = build, lift = lift, verify = verify)
        catch e
            e isa RischNotImplemented || rethrow()
        end
        r = bioche(f, x; build = build, lift = lift)    # rational in sin u, cos u (step TS)
        r === nothing || return r
    end
    T, el = build_tower(f, xk)
    bd = Builder(build === nothing ? auto_build(f, x) : build,
                 lift === nothing ? auto_lift(f, x) : lift, x, T.consts)
    try
        integrate_built(T, el, bd, verify)
    catch e
        # the structure-theorem arguments behind some decisions are for exp/log towers only (TA)
        (e isa NotElementary && any(lv -> lv.kind === :atan, T.levels)) || rethrow()
        throw(RischNotImplemented("not decided with atan in the tower: " * e.msg))
    end
end

# integrate an element of a built tower and return the term (base variable printed as bd.x)
function integrate_built(T::Tower, el, bd::Builder, verify::Bool; pos = nothing)
    L = length(T.levels)
    if is_complex_field(ctype(T))      # Step 7: integrate over ℚ(i), then take the real part
        res = integrate_el(T, L, el)
        verify && !check_tower(T, L, res, el) &&
            throw(RischError("internal check failed: derivative of the result differs from the integrand"))
        isrsc(q) = q isa TowerRootSum || q isa BaseRootSum
        any(isrsc, res.quads) || return to_term_real(bd, T, L, res, el; pos = pos)
        # step RC: RootSums over ℚ(i) stay complex (F(a) takes the real part); the elementary part
        # is put in real form and checked against f - Re(Σ RootSum′), Re = (d + σd)/2
        kinds = sigma_kinds(T)
        rss = Any[complex_term_rootsum(bd, T, kinds, q) for q in res.quads if isrsc(q)]
        drs = sum(liftto(T, q.deriv, L) for q in res.quads if isrsc(q))
        re = (drs + tconj(T, kinds, drs, L)) * lconst(T, inv(cfromQ(ctype(T), Q(2))), L)
        el_part = ElemIntegral(res.v, res.logs, res.atans, Any[q for q in res.quads if !isrsc(q)])
        return IntegralWithRootSums(to_term_real(bd, T, L, el_part, liftto(T, el, L) - re), rss, string(bd.x))
    end
    if L > 0
        res = integrate_el(T, L, el)
        verify && !check_tower(T, L, res, el) &&
            throw(RischError("internal check failed: derivative of the result differs from the integrand"))
        if pos !== nothing && ctype(T) === Q && all(φ -> φ isa Frac{UPoly{Q}}, pos)   # step TL
            res = real_logs_tower(T, res, pos)
            verify && !check_tower(T, L, res, el) &&
                throw(RischError("internal check failed: derivative of the result (real log form) differs from the integrand"))
        end
        isrs(q) = q isa TowerRootSum || q isa BaseRootSum
        any(isrs, res.quads) || return to_term(bd, T, res)
        rss = Any[q isa BaseRootSum ?
                  (ctype(T) === Q ? RootSum{Q}(q.rs.poly, q.rs.W, string(bd.x), bd.x) : base_term_rootsum(bd, q.rs)) :
                  TermRootSum(bd, T, q) for q in res.quads if isrs(q)]
        el_part = ElemIntegral(res.v, res.logs, res.atans, Any[q for q in res.quads if !isrs(q)])
        return IntegralWithRootSums(to_term(bd, T, el_part), rss, string(bd.x))
    end
    F = el                              # an element of K_0 = C(x)
    res = integrate_rational(F)
    if !isempty(res.unresolved)
        C = ctype(T)
        (C === Q || rational_tfield(C)) || throw(RischNotImplemented(
            "the logarithmic part has residues of degree > 2 over the constant field $C " *
            "(RootSum is implemented over ℚ and ℚ(t₁, …) only)"))
        rss = RootSum[]                 # algebraic residues of degree > 2: RootSum
        for (rest, R, D) in res.unresolved
            append!(rss, root_sums(rest, R, D, string(bd.x); arg = bd.x))
        end
        el_part = RationalIntegral(res.rational, res.logs, res.atans, Any[], res.quads)
        verify && derivative_of(el_part) + sum(rootsum_derivative(rs) for rs in rss) != F &&
            throw(RischError("internal check failed: derivative of the result (with RootSums) differs from the integrand"))
        out = C === Q ? Any[rs for rs in rss] : Any[base_term_rootsum(bd, rs) for rs in rss]   # step RE
        return IntegralWithRootSums(to_term(bd, el_part), out, string(bd.x))
    end
    verify && !check_result(res, F) &&
        throw(RischError("internal check failed: derivative of the result differs from the integrand"))
    if pos !== nothing && ctype(T) === Q && all(φ -> φ isa Frac{UPoly{Q}}, pos)   # RL, EL: real log arguments
        res = real_logs_on(res, pos)
        verify && !check_result(res, F) &&
            throw(RischError("internal check failed: derivative of the result (real log form) differs from the integrand"))
    end
    to_term(bd, res)
end

# --- iterated integrals (step IT) ----------------------------------------------------
# a leaf that is a symbol (not a number, e or π)
has_symbol(t) = safe_iscall(t) && !isempty(arguments(t)) ? any(has_symbol, arguments(t)) :
                (leaf_rational(t) === nothing && !is_e_const(t) && !(string(t) in ("pi", "π")))
# f = c·g with c ≠ 1 the product of the factors of f (numerator and denominator of a top-level
# product or quotient) that are free of x but contain a symbol: (c, g, builder), or nothing
function split_free_factor(f, x, xk::String, build, lift)
    (safe_iscall(f) && !isempty(arguments(f))) || return nothing
    n = opname(operation(f))
    n in (:*, :/) || return nothing
    factors(t) = (safe_iscall(t) && !isempty(arguments(t)) && opname(operation(t)) === :*) ? arguments(t) : Any[t]
    nums, dens = n === :* ? (Any[arguments(f)...], Any[]) :
                 length(arguments(f)) == 2 ? (Any[factors(arguments(f)[1])...], Any[factors(arguments(f)[2])...]) :
                 return nothing
    isfree(t) = !has_leaf(t, xk) && has_symbol(t)
    cn, cd = filter(isfree, nums), filter(isfree, dens)
    (isempty(cn) && isempty(cd)) && return nothing
    gn, gd = filter(!isfree, nums), filter(!isfree, dens)
    (isempty(gn) && isempty(gd)) && return nothing           # f free of x altogether: as before
    bd = Builder(build === nothing ? auto_build(f, x) : build, lift === nothing ? auto_lift(f, x) : lift, x)
    prod_(ts) = isempty(ts) ? bd.lift(1) : length(ts) == 1 ? ts[1] : mk(bd, :*, ts...)
    c = isempty(cd) ? prod_(cn) : mk(bd, :/, prod_(cn), prod_(cd))
    g = isempty(gd) ? prod_(gn) : mk(bd, :/, prod_(gn), prod_(gd))
    (c, g, bd)
end

# ∫ (E + Σ RootSums) dy for an `IntegralWithRootSums` (e.g. the second integral of
# `integrate(f, x, y)`): E by `risch_integrate` (x is then a parameter, step SY), and a RootSum that
# does not involve y integrates to y·RootSum exactly (`ScaledRootSum`). A RootSum depending on y
# (its roots or W involve y) is refused.
struct ScaledRootSum
    factor::Any                         # a term of the user's package
    rs::Any                             # RootSum, TermRootSum or ScaledRootSum
end
Base.show(io::IO, s::ScaledRootSum) = print(io, "(", s.factor, ")*", s.rs)
rs_value(s::ScaledRootSum, xk::String, a) = term_value(s.factor, xk, a) * rs_value(s.rs, xk, a)
rs_value_continuous(s::ScaledRootSum, xk::String, a::Real) = term_value(s.factor, xk, a) * rs_value_continuous(s.rs, xk, a)

has_leaf(t, yk::String) = safe_iscall(t) && !isempty(arguments(t)) ? any(a -> has_leaf(a, yk), arguments(t)) :
                          string(t) == yk
depends_on(rs::RootSum, yk::String) = rs.var == yk || (rs.arg !== nothing && has_leaf(rs.arg, yk))
depends_on(rs::TermRootSum, yk::String) =
    rs.var == yk || any(c -> c !== nothing && (c isa Tuple ? any(t -> t !== nothing && has_leaf(t, yk), c) : has_leaf(c, yk)),
                        rs.coeffs) || (rs.pterms !== nothing && any(t -> has_leaf(t, yk), rs.pterms))
depends_on(s::ScaledRootSum, yk::String) = has_leaf(s.factor, yk) || depends_on(s.rs, yk)

function risch_integrate(F::IntegralWithRootSums, y; build = nothing, lift = nothing, verify::Bool = true)
    yk = string(y)
    scaled = Any[]
    for rs in F.rootsums
        if !depends_on(rs, yk)
            push!(scaled, ScaledRootSum(y, rs))                # ∂/∂y (y·RS) = RS
        elseif rs isa ScaledRootSum && !depends_on(rs.rs, yk)   # c(y)·RS: (∫ c dy)·RS
            nf = risch_integrate(rs.factor, y; build = build, lift = lift, verify = verify)
            nf isa IntegralWithRootSums && throw(RischNotImplemented(
                "integrating a RootSum times a factor whose integral is a RootSum"))
            push!(scaled, ScaledRootSum(nf, rs.rs))
        else
            throw(RischNotImplemented("integrating a RootSum whose roots or logarithms depend on $yk"))
        end
    end
    E = risch_integrate(F.elementary, y; build = build, lift = lift, verify = verify)
    E isa IntegralWithRootSums ? IntegralWithRootSums(E.elementary, vcat(E.rootsums, scaled), yk) :
                                 IntegralWithRootSums(E, scaled, yk)
end
