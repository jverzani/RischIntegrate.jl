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
        r = integrate_direct(f, x; build = build, lift = lift, verify = verify)
        # a RootSum over a parameter field: a homogeneous f scales to ℚ (step PS)
        if r isa IntegralWithRootSums && any(t -> t isa TermRootSum, r.rootsums) && has_param(f, string(x))
            r2 = integrate_param_scaled(f, x; build = build, lift = lift, verify = verify)
            r2 === nothing || return r2
        end
        r
    catch e
        # the term type has no method for a special function of the answer: through Expr, the special terms
        # evaluated numerically
        if e isa MethodError && any(fn -> e.f === fn, SPECIAL_FNS) && !(f isa Expr)
            return integrate_special_fallback(f, x; build = build, lift = lift, verify = verify)
        end
        (e isa RischNotImplemented || e isa NotElementary) || rethrow()
        if e isa NotElementary && HYP_ANSWERS[]           # xˢ e^(bx+d): incomplete gamma (phase 6, H3)
            g = try_gamma(f, x; build = build, lift = lift, verify = verify)
            g === nothing || return g
            g = try_gamma_log(f, x; build = build, lift = lift, verify = verify)
            g === nothing || return g
            g = try_trig_power(f, x; build = build, lift = lift, verify = verify)   # xˢ sin, cos (H4)
            g === nothing || return g
        end
        r = try_usub(f, x; build = build, lift = lift, verify = verify)    # step US
        r === nothing || return r
        # a u-substitution may have failed only for want of a special function in the term type: once
        # through Expr, keeping the answer when it has special terms
        if !(f isa Expr) && !EXPR_RETRY[]
            EXPR_RETRY[] = true
            r2 = try
                integrate_special_fallback(f, x; build = build, lift = lift, verify = verify)
            catch e2
                (e2 isa RischNotImplemented || e2 isa NotElementary) || rethrow()
                nothing
            finally
                EXPR_RETRY[] = false
            end
            (r2 isa IntegralWithRootSums && any(t -> t isa ExprTerm, r2.rootsums)) && return r2
        end
        throw(e)
    end
end
const EXPR_RETRY = Ref(false)                           # no nested Expr retries

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
    g = expand_trig_shifts(f, x, xk, build, lift)      # sin(v + a) = sin v cos a + cos v sin a (step TS2)
    g === nothing || return risch_integrate(g, x; build = build, lift = lift, verify = verify)
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
    if any(((_, u),) -> has_param(u, xk), rads)        # parameters in a radicand: x = s u + h (step PR)
        r = integrate_param_radicals(f, x, rads; build = build, lift = lift, verify = verify)
        r === nothing || return r
    end
    if any(((_, u),) -> radicand_element(u, xk) === nothing, rads)
        # radicals of functions of e^(kx), cos kx, sin kx, tan kx: substitute s (step MR)
        r = try
            integrate_monomial_radicals(f, x; build = build, lift = lift, verify = verify)
        catch e
            e isa RischNotImplemented || rethrow()
            nothing
        end
        r === nothing || return r
        r = try                                          # perfect powers at a finer monomial (step PW)
            integrate_power_radicands(f, x; build = build, lift = lift, verify = verify)
        catch e
            e isa RischNotImplemented || rethrow()
            nothing
        end
        r === nothing || return r
        # nested square roots that denest (step DN): rewrite, then integrate the ordinary radicals
        bd = Builder(build === nothing ? auto_build(f, x) : build, lift === nothing ? auto_lift(f, x) : lift, x)
        g = denest_rewrite(f, xk, bd)
        g === nothing || return risch_integrate(g, x; build = build, lift = lift, verify = verify)
        r = integrate_nested(f, x, xk, bd; verify = verify)    # √(a + b√c) with a² - b²c = -s²
        r === nothing || return r
    end
    if !isempty(rads)                  # a RootSum is in the substitution variable t: evaluate through x
        F = try
            integrate_radical(f, x, rads; build = build, lift = lift, verify = verify)
        catch e
            e isa RischNotImplemented || rethrow()
            try                                         # products of radicals of any index (SI2 phase 3a)
                integrate_kummer(f, x, rads; build = build, lift = lift, verify = verify)
            catch e2
                e2 isa RischNotImplemented || rethrow()
                throw(occursin("phase 3b", e2.msg) ? e2 : e)
            end
        end
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
        return with_rootsums(bd, to_term(bd, T, el_part), rss)
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
        return with_rootsums(bd, to_term(bd, el_part), out)
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

# the elementary part with RootSums; RootSums written out as terms (step PQ) join the elementary part
function with_rootsums(bd::Builder, E, rss)
    ts = Any[r for r in rss if !(r isa TermRootSum || r isa RootSum)]
    rs = Any[r for r in rss if r isa TermRootSum || r isa RootSum]
    isempty(ts) || (E = mk(bd, :+, E, ts...))
    isempty(rs) ? E : IntegralWithRootSums(E, rs, string(bd.x))
end

# step TS2: a trigonometric or hyperbolic function of v + c, c free of x with parameters (sin(x + a)):
# the addition formulas, so that cos c, sin c (cosh c, sinh c) are opaque constants (`parse_tower`).
# Returns the rewritten term, or nothing when there is no such shift.
const SHIFT_TRIG = (:sin, :cos, :tan, :cot, :sec, :csc, :sinh, :cosh, :tanh, :coth, :sech, :csch)
function expand_trig_shifts(f, x, xk::String, build, lift)
    has_shift(t) = safe_iscall(t) && !isempty(arguments(t)) &&
        ((opname(operation(t)) in SHIFT_TRIG && length(arguments(t)) == 1 && shift_split(arguments(t)[1], xk) !== nothing) ||
         any(has_shift, arguments(t)))
    has_shift(f) || return nothing
    b = Builder(build === nothing ? auto_build(f, x) : build, lift === nothing ? auto_lift(f, x) : lift, x)
    function rw(t)
        (safe_iscall(t) && !isempty(arguments(t))) || return t
        args = Any[rw(a) for a in arguments(t)]
        n = opname(operation(t))
        sp = (n in SHIFT_TRIG && length(args) == 1) ? shift_split(args[1], xk) : nothing
        sp === nothing && return b.build(op_function(t), args...)
        sumt(l) = (ts = Any[sg == 1 ? c : mk(b, :*, b.lift(-1), c) for (c, sg) in l]; length(ts) == 1 ? ts[1] : mk(b, :+, ts...))
        v, c = sumt(sp[1]), sumt(sp[2])
        hyp = n in (:sinh, :cosh, :tanh, :coth, :sech, :csch)
        S, Cs = hyp ? (:sinh, :cosh) : (:sin, :cos)
        sv, cv = b.build(OPS_HYP[S], v), b.build(OPS_HYP[Cs], v)
        kπ = hyp ? nothing : pi_multiple(sp[2])
        cc, sc = kπ !== nothing ? exact_cos_sin(b, kπ) : (b.build(OPS_HYP[Cs], c), b.build(OPS_HYP[S], c))
        sn = mk(b, :+, mk(b, :*, sv, cc), mk(b, :*, cv, sc))                      # sin(v + c)
        cs = hyp ? mk(b, :+, mk(b, :*, cv, cc), mk(b, :*, sv, sc)) :            # cosh(v + c)
                   mk(b, :+, mk(b, :*, cv, cc), mk(b, :*, b.lift(-1), sv, sc))  # cos(v + c)
        n in (:sin, :sinh) && return sn
        n in (:cos, :cosh) && return cs
        n in (:tan, :tanh) && return mk(b, :/, sn, cs)
        n in (:cot, :coth) && return mk(b, :/, cs, sn)
        n in (:sec, :sech) && return mk(b, :/, b.lift(1), cs)
        mk(b, :/, b.lift(1), sn)
    end
    rw(f)
end
const OPS_HYP = Dict{Symbol,Function}(:sin => sin, :cos => cos, :sinh => sinh, :cosh => cosh)
# u = v + c with v ∋ x and c ≠ 0 free of x with a parameter: the summands of (v, c), else nothing
function shift_split(u, xk::String)
    (safe_iscall(u) && opname(operation(u)) in (:+, :-)) || return nothing
    vs, cs = Any[], Any[]
    neg = opname(operation(u)) === :-
    for (j, a) in enumerate(arguments(u))
        sg = (neg && (j > 1 || length(arguments(u)) == 1)) ? -1 : 1
        push!(has_x(a, xk) ? vs : cs, (a, sg))
    end
    (isempty(vs) || isempty(cs) || !(any(((c, _),) -> has_param(c, xk), cs) || pi_multiple(cs) !== nothing)) && return nothing
    vs, cs
end
# Σ cs = r·π with r rational, 12r an integer, and an exact cos, sin (multiples of π/6, π/4): 12r, else nothing
function pi_multiple(cs)
    any(((c, _),) -> has_param(c, "\0"), cs) && return nothing   # (π is not a parameter)
    v = try
        sum(sg * term_value(c, "\0", 0.0) for (c, sg) in cs) / π
    catch
        return nothing
    end
    (isfinite(real(v)) && abs(imag(v)) < 1e-12) || return nothing
    k = round(Int, 12 * real(v))
    (abs(12 * real(v) - k) < 1e-9 && (k % 2 == 0 || k % 3 == 0)) || return nothing
    k
end
# (cos, sin) of kπ/12 (k even or a multiple of 3) as terms q·√s
function exact_cos_sin(b::Builder, k::Int)
    d = mod(15 * k, 360)
    base = Dict(0 => ((1, 1), (0, 1)), 30 => ((1 // 2, 3), (1 // 2, 1)), 45 => ((1 // 2, 2), (1 // 2, 2)),
                60 => ((1 // 2, 1), (1 // 2, 3)), 90 => ((0, 1), (1, 1)))
    q = d ÷ 90                                          # quadrant: rotate by 90° q times
    (cq, sq) = base[d - 90q]
    for _ in 1:q
        cq, sq = ((-sq[1], sq[2]), cq)
    end
    t((r, sv)) = iszero(r) ? b.lift(0) : isone(sv) ? cterm(b, Q(r)) :
                 isone(r) ? mk(b, :sqrt, b.lift(sv)) : mk(b, :*, cterm(b, Q(r)), mk(b, :sqrt, b.lift(sv)))
    t(cq), t(sq)
end
