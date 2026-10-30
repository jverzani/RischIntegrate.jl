# ---------------------------------------------------------------------------
# Public API
# ---------------------------------------------------------------------------
"""
    risch_integrate(f, x; build = nothing, lift = nothing, verify = true, signs = (), sign = nothing)

The antiderivative of the term `f` in the variable `x` (the function behind [`integrate`](@ref)).
`build` and `lift` control how the answer is built as a term; `verify = false` skips the final
check of the answer by differentiation (every answer is checked by default). Returns a term, or an
[`IntegralWithRootSums`](@ref); throws [`NotElementary`](@ref) or [`RischNotImplemented`](@ref).

Some forms depend on the sign of an expression in the parameters (symbols other than `x`): `atan`
or `log`, which square root. Signs can be given, as in GruntzLimit, by `signs`: pairs `c => s`, with
`c` a parameter or an expression in the parameters written like `f`, and `s` one of `:positive`,
`:negative` or `:nonzero`. GruntzLimit's `:zero`, `:nonnegative` and `:nonpositive` are an
`ArgumentError`: a zero value is a special case of the parameters, which is not treated. The sign of an expression is then taken from a fact about a rational multiple of it, from
the signs of its terms, or from a product of the facts' expressions. More generally, `sign(p)` is
called with the expression `p`, a term built like the answer, and returns `1`, `-1`, `0` or
`nothing` (undecided); it is asked before `signs`. It is also asked about the argument `w` of each
logarithm `c log(w)` in the answer (an expression in `x`, on the caller's domain): for `-1` the
answer has `log(-w)`, real there. Otherwise `log(w)` stays, complex where `w < 0` (it differs from a
real antiderivative by a constant there, as in Mathematica's answers). Undecided signs are taken with the `k`-th
parameter (alphabetically) set to `k`, or to `-k` when that parameter is known to be negative.
A `0` for an expression that is not identically zero is a special case of the parameters, not
treated (`RischNotImplemented`).

```julia
risch_integrate(:(1/(x^2 + a)), :x; signs = Dict(:a => :negative))
```
"""
Base.@nospecializeinfer function risch_integrate(@nospecialize(f), @nospecialize(x); build = nothing, lift = nothing,
                                                  verify::Bool = true, signs = (), sign = nothing)
    if !isempty(signs)                                                 # step SO
        F = SignFacts(signs)
        g = sign === nothing ? (p -> facts_sign(F, p)) : (p -> (s = sign(p); s === nothing ? facts_sign(F, p) : s))
        return risch_integrate(f, x; build = build, lift = lift, verify = verify, sign = g)
    end
    if sign !== nothing
        o = SignOracle(sign, build === nothing ? auto_build(f, x) : build, lift === nothing ? auto_lift(f, x) : lift,
                       x, Dict{Any,Union{Int,Nothing}}())
        return try
            Base.ScopedValues.with(SIGN_ORACLE => o) do
                F = risch_integrate(f, x; build = build, lift = lift, verify = verify)
                F isa IntegralWithRootSums ? F : oracle_real_logs(F, Builder(o.build, o.lift, x), string(x), o)
            end
        catch err
            err isa SignOracleZero ? throw(RischNotImplemented(err.msg)) : rethrow()
        end
    end
    check_leaves(f, string(x))                                         # step WR
    try
        r = integrate_direct(f, x; build = build, lift = lift, verify = verify)
        # a RootSum over a parameter field: a homogeneous f scales to ℚ (step PS)
        if r isa IntegralWithRootSums && any(t -> t isa TermRootSum, r.rootsums) && has_param(f, string(x))
            r2 = integrate_param_scaled(f, x; build = build, lift = lift, verify = verify)
            r2 === nothing || return r2
        end
        # a RootSum for a binomial denominator xⁿ + c: x = |c|^(1/n) u (step BN)
        if r isa IntegralWithRootSums
            r2 = integrate_binomial_scaled(f, x; build = build, lift = lift, verify = verify)
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
        g = try
            # x·R(sin, cos): Clausen's function (step CL); logʲ(x) L(w x)/x, L = atan, log or li2: polylogarithms
            # by parts (step LP, before step AT: ∫ atan(x)/x = Ti₂(x), not eight Clausen terms); atan(u): u = tan t
            # (step AT), else by parts (step AP)
            g1 = e isa NotElementary ? try_x_trig(f, x; build = build, lift = lift, verify = verify) : nothing
            g1 === nothing && (g1 = try_log_polylog(f, x; build = build, lift = lift, verify = verify))
            g1 === nothing && (g1 = try_atan_subst(f, x; build = build, lift = lift, verify = verify))
            g1 === nothing ? try_parts(f, x; build = build, lift = lift, verify = verify) : g1
        catch e2
            # (raised here, inside the catch, these miss the special-function fallback above)
            (e2 isa MethodError && any(fn -> e2.f === fn, SPECIAL_FNS) && !(f isa Expr)) || rethrow()
            integrate_special_fallback(f, x; build = build, lift = lift, verify = verify)
        end
        g === nothing || return g
        if e isa NotElementary && HYP_ANSWERS[]           # xᵐ(α + βxⁿ)^q, sinᵖ cosʳ, symbolic exponents: ₂F₁ (step HS)
            g = try
                g1 = try_binomial_symbolic(f, x; build = build, lift = lift, verify = verify)
                g1 === nothing && (g1 = try_trig_symbolic(f, x; build = build, lift = lift, verify = verify))
                # e^(ax) R(cos bx, sin bx): Re ₂F₁(k, s; s + 1; E/r) (step EH)
                g1 === nothing ? try_exp_trig_hyp(f, x; build = build, lift = lift, verify = verify) : g1
            catch e2
                (e2 isa MethodError && any(fn -> e2.f === fn, SPECIAL_FNS) && !(f isa Expr)) || rethrow()
                integrate_special_fallback(f, x; build = build, lift = lift, verify = verify)
            end
            g === nothing || return g
        end
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
        r = try_nested_radical(f, x; build = build, lift = lift, verify = verify)   # nested radicals (step NS)
        r === nothing || return r
        r = try_const_scaling(f, x; build = build, lift = lift, verify = verify)   # … over ℚ(√d) (step CS)
        r === nothing || return r
        r = try_pair_radical(f, x; build = build, lift = lift, verify = verify)   # √(g + c₁), √(g + c₂) (step PP)
        r === nothing || return r
        r = try_reciprocal(f, x; build = build, lift = lift, verify = verify)   # u = x + s/x (step RC)
        r === nothing || return r
        r = try_tower_radical(f, x; build = build, lift = lift, verify = verify)   # √ of a tower element (step RY)
        r === nothing || return r
        r = try_sum_split(f, x; build = build, lift = lift, verify = verify)   # term by term (step LS)
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
    @nospecialize f x
    xk = string(x)
    g = merge_exp_powers(f, x, build, lift)            # (bʷ)^r = b^(w r), b > 0 constant (step EP)
    g === nothing || return risch_integrate(g, x; build = build, lift = lift, verify = verify)
    g = try_erf(f, x; build = build, lift = lift, verify = verify)   # ∫ erf(ax + b) by parts
    g === nothing || return g
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
    r = try                                            # sin(e + f x): y = e + f x (step TL)
        integrate_linear_shift(f, x; build = build, lift = lift, verify = verify)
    catch e
        e isa RischNotImplemented || rethrow()         # (refused in y: the addition formulas may still do)
        nothing
    end
    r === nothing || return r
    g = expand_trig_shifts(f, x, xk, build, lift)      # sin(v + a) = sin v cos a + cos v sin a (step TS2)
    g === nothing || return risch_integrate(g, x; build = build, lift = lift, verify = verify)
    has_op(f, :acot) && return risch_integrate(rewrite_acot(f, x, build, lift), x; build = build, lift = lift,
                                               verify = verify)     # acot(u) = atan(1/u) (step AC)
    if any(n -> has_op(f, n), INV_HYP)
        # A·L by parts first, so the answer keeps L (∫ asinh x = x asinh x - √(x² + 1), step AP), else
        # atanh, acoth, asinh, acosh, acsch, asech as logs (step IH)
        r = try_parts(f, x; build = build, lift = lift, verify = verify)
        r === nothing || return r
        return risch_integrate(rewrite_invhyp(f, x, build, lift), x; build = build, lift = lift, verify = verify)
    end
    arcs = collect_arcs(f, xk)                  # asin / acos: substitution u = sin t / cos t (step AS)
    if !isempty(arcs)
        r = integrate_arcs_scaled(f, x, arcs; build = build, lift = lift, verify = verify)   # asin(a x): y = a x (AL)
        r === nothing || return r
        return integrate_arcsin(f, x, arcs; build = build, lift = lift, verify = verify)
    end
    rads = collect_radicals(f, xk)
    if isempty(rads) && has_param(f, xk)               # a power of one parameter quadratic: linearity (step PL)
        r = integrate_param_linear(f, x; build = build, lift = lift, verify = verify)
        r === nothing || return r
    end
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
    if !OPAQUE_CONST_RADICALS[] && length(rads) >= 1 && all(((e, u),) -> denominator(e) == 2 && string(u) == string(rads[1][2]), rads)
        # one quadratic radicand K - |α| (x - h)² over ℚ whose scaling to K(1 - u²) is irrational (7 - 2x²:
        # s = √(7/2)): step PR with the constant radicals opaque, so that the asin route applies to the
        # integrand in u
        q = radicand_element(rads[1][2], xk)
        irrational_scale = q !== nothing && isone(q.den) && degree(q.num) == 2 && begin
            γ, β, α = q.num.c
            K = γ - β^2 / (4α)
            # (the asin family only, α < 0 < K: for α > 0 the Euler substitutions keep real log arguments, step EL)
            α < 0 && K > 0 && (rat_sqrt(K) === nothing || rat_sqrt(-K / α) === nothing)
        end
        # (P(x)·(radical)^k only: other poles give log parts with √K, √(K/|α|) as opaque constants, where
        # √K² = K is not seen; those keep the usual route)
        irrational_scale && (irrational_scale = poly_times_radicals(f, xk, rads[1][2]))
        if irrational_scale
            OPAQUE_CONST_RADICALS[] = true
            r = try
                integrate_param_radicals(f, x, rads; build = build, lift = lift, verify = verify, rational = true)
            catch e
                (e isa RischNotImplemented || e isa NotElementary) || rethrow()
                nothing
            finally
                OPAQUE_CONST_RADICALS[] = false
            end
            r === nothing || return r
        end
    end
    if any(((_, u),) -> has_param(u, xk), rads)        # parameters in a radicand: x = s u + h (step PR)
        r = integrate_param_repeated(f, x, rads; build = build, lift = lift, verify = verify)   # u = sⁿ w (PM)
        r === nothing || return r
        g = rewrite_two_linear(f, x, rads; build = build, lift = lift)   # (a + bx)^E₁ (c + dx)^E₂, E₁ + E₂ ∈ ℤ (LL)
        if g !== nothing
            r = try
                risch_integrate(g, x; build = build, lift = lift, verify = verify)
            catch e
                (e isa RischNotImplemented || e isa NotElementary) || rethrow()
                nothing
            end
            r === nothing || return r
        end
        r = integrate_param_radicals(f, x, rads; build = build, lift = lift, verify = verify)
        r === nothing || return r
        r = try                                          # several radicands, one linear: u = √(linear) (NR)
            integrate_inner_linear_radical(f, x; build = build, lift = lift, verify = verify)
        catch e
            (e isa RischNotImplemented || e isa NotElementary) || rethrow()
            nothing
        end
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
        r = try                                          # an innermost radical of a linear radicand (step NR)
            integrate_inner_linear_radical(f, x; build = build, lift = lift, verify = verify)
        catch e
            (e isa RischNotImplemented || e isa NotElementary) || rethrow()
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
        verify && !check_with_rootsums(el_part, rss, F) &&
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
# a root c^(p/q) with q > 2 of a constant (2^(1/4) from step CS): the constant fields hold square roots only
has_high_root(t) = safe_iscall(t) && !isempty(arguments(t)) &&
                   ((rp = radical_parts(t); rp !== nothing && denominator(rp[1]) > 2) || any(has_high_root, arguments(t)))
# f = c·g with c ≠ 1 the product of the factors of f (numerator and denominator of a top-level
# product or quotient) that are free of x but contain a symbol or a root c^(p/q), q > 2: (c, g, builder), or nothing
function split_free_factor(f, x, xk::String, build, lift)
    @nospecialize f x
    (safe_iscall(f) && !isempty(arguments(f))) || return nothing
    n = opname(operation(f))
    n in (:*, :/) || return nothing
    factors(t) = (safe_iscall(t) && !isempty(arguments(t)) && opname(operation(t)) === :*) ? arguments(t) : Any[t]
    nums, dens = n === :* ? (Any[arguments(f)...], Any[]) :
                 length(arguments(f)) == 2 ? (Any[factors(arguments(f)[1])...], Any[factors(arguments(f)[2])...]) :
                 return nothing
    isfree(t) = !has_leaf(t, xk) && (has_symbol(t) || has_high_root(t))
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

# an answer with its variable substituted (a substitution step putting u back): the elementary part by the term
# map `back`, a RootSum with its variable standing for back(x) (`arg`), a TermRootSum with `back` applied to its
# coefficients; nothing when a part cannot be substituted (an `ExprTerm`)
function subst_answer(F, back, bd::Builder)
    F isa IntegralWithRootSums || return back(F)
    rss = Any[rootsum_subst(r, back, bd) for r in F.rootsums]
    any(isnothing, rss) && return nothing
    IntegralWithRootSums(back(F.elementary), rss, F.var)
end
rootsum_subst(r::TermRootSum, back, bd::Builder) =
    TermRootSum(r.poly, Any[c === nothing ? nothing : c isa Tuple ? map(t -> t === nothing ? nothing : back(t), c) : back(c)
                            for c in r.coeffs], r.var, r.pterms)
function rootsum_subst(r::ScaledRootSum, back, bd::Builder)
    s = rootsum_subst(r.rs, back, bd)
    s === nothing ? nothing : ScaledRootSum(back(r.factor), s)
end
function rootsum_subst(r::RootSum{C}, back, bd::Builder) where {C}
    a = back(r.arg === nothing ? bd.x : r.arg)
    RootSum{C}(r.poly, r.W, safe_iscall(a) ? "($a)" : string(a), a)
end
rootsum_subst(r, back, bd::Builder) = nothing

# the sum of answers, some of them with RootSums
function add_answers(bd::Builder, Fs, xk::String)
    els = Any[F isa IntegralWithRootSums ? F.elementary : F for F in Fs]
    E = length(els) == 1 ? els[1] : mk(bd, :+, els...)
    any(F -> F isa IntegralWithRootSums, Fs) || return E
    IntegralWithRootSums(E, Any[rs for F in Fs if F isa IntegralWithRootSums for rs in F.rootsums], xk)
end

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
    @nospecialize f x
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

# step TL: every trigonometric or hyperbolic argument with x is r·(e + f x), r rational, one of them with a
# parameter shift e (sin(e + f x)·cos(2e + 2f x)): y = e + f x, x = (y - e)/f, dx = dy/f, and y = e + f x is
# substituted back. Before step TS2, whose cos e, sin e are independent constants to the constant field
# (cos² e + sin² e = 1 is not seen: hidden zero denominators, false residue criteria, slow resultants).
# Nothing when there is no such form, or inside another step TL: a substitution below can bring the shift
# back (∫ (a + b asin(c x))^(-3/2): u = sin t, then cos((v - a)/b) for v = a + b t), and the two would undo
# each other until the stack overflows; the inner one is left to step TS2.
const LINEAR_SHIFT = Ref(false)
function integrate_linear_shift(f, x; build = nothing, lift = nothing, verify::Bool = true)
    @nospecialize f x
    LINEAR_SHIFT[] && return nothing
    xk = string(x)
    # the arguments; x elsewhere only algebraically (exp(c x) would become exp(c (y - e)/f))
    args = Any[]
    function collect_args(t)
        (safe_iscall(t) && !isempty(arguments(t))) || return true
        n = opname(operation(t))
        if n in SHIFT_TRIG && length(arguments(t)) == 1 && has_x(arguments(t)[1], xk)
            push!(args, arguments(t)[1])
            return true
        end
        (n in (:+, :-, :*, :/, :^, :sqrt, :cbrt) || !has_x(t, xk)) || return false
        all(collect_args, arguments(t))
    end
    collect_args(f) || return nothing
    j = findfirst(a -> (sp = shift_split(a, xk); sp !== nothing && pi_multiple(sp[2]) === nothing), args)
    j === nothing && return nothing
    L = args[j]
    bd = Builder(build === nothing ? auto_build(f, x) : build, lift === nothing ? auto_lift(f, x) : lift, x)
    pp = poly_parts(bd, L, xk)
    (pp === nothing || !haskey(pp, 1) || !haskey(pp, 0) || maximum(keys(pp)) != 1) && return nothing
    a, b = pp[1], pp[0]
    # the ratio of each argument to L: a rational constant
    ratio = Dict{String,Q}()
    for u in args
        haskey(ratio, string(u)) && continue
        T, el = try
            build_tower(mk(bd, :/, u, L), xk)
        catch e
            (e isa RischNotImplemented || e isa RischError) || rethrow()
            return nothing
        end
        (isempty(T.levels) && degree(el.num) == 0 && degree(el.den) == 0) || return nothing
        r = rational_const(el.num.c[1] / el.den.c[1])
        r === nothing && return nothing
        ratio[string(u)] = r
    end
    y = bd.x
    X = mk(bd, :/, mk(bd, :+, y, mk(bd, :*, bd.lift(-1), b)), a)
    function walk(t)
        isnode(t) || return string(t) == xk ? X : t
        if opname(operation(t)) in SHIFT_TRIG && length(arguments(t)) == 1 && haskey(ratio, string(arguments(t)[1]))
            r = ratio[string(arguments(t)[1])]
            return term_rebuild(bd, t, Any[isone(r) ? y : mk(bd, :*, cterm(bd, r), y)])
        end
        term_rebuild(bd, t, Any[walk(s) for s in arguments(t)])
    end
    g = mk(bd, :*, mk(bd, :^, a, bd.lift(-1)), walk(f))
    LINEAR_SHIFT[] = true
    G = try
        risch_integrate(g, x; build = build, lift = lift, verify = verify)
    finally
        LINEAR_SHIFT[] = false
    end
    back(t) = isnode(t) ? term_rebuild(bd, t, Any[back(s) for s in arguments(t)]) : (string(t) == xk ? L : t)
    subst_answer(G, back, bd)
end
# an element of a constant field (ℚ, ℚ(i), parameter fractions over them) that is rational, else nothing
rational_const(v::Q) = v
rational_const(v::QI) = iszero(v.im) ? v.re : nothing
rational_const(v::Frac{<:UPoly}) = (degree(v.num) == 0 && degree(v.den) == 0) ?
    (n = rational_const(v.num.c[1]); d = rational_const(v.den.c[1]); n === nothing || d === nothing ? nothing : n / d) : nothing
rational_const(v) = nothing
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

# f is a polynomial in x with coefficients involving the radicals of radicand ut only (no other poles)
function poly_times_radicals(f, xk::String, ut)
    us = string(ut)
    hook(t, T) = (rp = isnode(t) ? radical_parts(t) : nothing; (rp !== nothing && string(rp[2]) == us) ? sym_const(T, t) : nothing)
    T, el = try
        build_tower(f, xk; subst = hook)
    catch e
        (e isa RischNotImplemented || e isa RischError) || rethrow()
        return false
    end
    isempty(T.levels) && degree(el.den) == 0
end
