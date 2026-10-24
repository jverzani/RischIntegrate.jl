# ---------------------------------------------------------------------------
# Step US: u-substitution (derivative-divides), tried when the direct routes fail
#
# For a subterm u of f: if f = G(u)·u' with G free of x, then ∫ f dx = (∫ G(U) dU) at U = u.
# The test is exact: q = f/u' (u' by the chain rule on terms) is parsed into a tower over x in
# which u, and every subterm whose x occurs only inside u, is an opaque constant (a `:sym`
# generator, step SY); q must be a constant there. Sound because the opaque constants are formally
# independent: an identity between the formal expressions stays true when the actual functions
# (of u only) are put back. For u = v^e (a radical) also v = U^(1/e) and v^(ke) = U^k, for
# u = x^k also x^(mk) = U^m. G is the constant printed with u ↦ x (the variable x stands for U,
# as in `integrate_arcsin`), integrated in x (verified there), and the answer printed with x ↦ u.
# ---------------------------------------------------------------------------
const USUB_DEPTH = Ref(0)       # nesting of substitutions (at most 2)

isnode(t) = safe_iscall(t) && !isempty(arguments(t))
depends_on(t, xk::String) = isnode(t) ? any(a -> depends_on(a, xk), arguments(t)) : string(t) == xk

# the derivative of the term t in x by the chain rule, `nothing` if t is free of x
function term_deriv(bd::Builder, t, xk::String)
    @nospecialize t
    depends_on(t, xk) || return nothing
    isnode(t) || return bd.lift(1)
    n, a = opname(operation(t)), arguments(t)
    d = Any[term_deriv(bd, s, xk) for s in a]
    neg(v) = mk(bd, :*, bd.lift(-1), v)
    mul(vs...) = length(vs) == 1 ? vs[1] : mk(bd, :*, vs...)
    if n === :+
        ds = Any[v for v in d if v !== nothing]
        return length(ds) == 1 ? ds[1] : mk(bd, :+, ds...)
    elseif n === :- && length(a) == 1
        return neg(d[1])
    elseif n === :- && length(a) == 2
        d[2] === nothing && return d[1]
        return d[1] === nothing ? neg(d[2]) : mk(bd, :+, d[1], neg(d[2]))
    elseif n === :*
        ts = Any[mul(Any[j == i ? d[i] : a[j] for j in eachindex(a)]...) for i in eachindex(a) if d[i] !== nothing]
        return length(ts) == 1 ? ts[1] : mk(bd, :+, ts...)
    elseif n === :/ && length(a) == 2
        d[2] === nothing && return mk(bd, :/, d[1], a[2])
        r = neg(mk(bd, :/, mul(a[1], d[2]), mk(bd, :^, a[2], bd.lift(2))))
        return d[1] === nothing ? r : mk(bd, :+, mk(bd, :/, d[1], a[2]), r)
    elseif n === :^ && length(a) == 2
        if d[2] === nothing
            p = leaf_rational(a[2])
            if p !== nothing && isone(denominator(p))           # (b^p)' = p b^(p-1) b'
                pm = mk(bd, :^, a[1], bd.lift(numerator(p) - 1))
                return mul(a[2], numerator(p) == 2 ? mul(a[1], d[1]) : mul(pm, d[1]))
            end
            return mul(a[2], t, mk(bd, :/, d[1], a[1]))        # radicals: p b^p b'/b (keeps the radical)
        elseif is_e_const(a[1])
            return mul(t, d[2])
        end
    elseif length(a) == 1
        n === :sqrt && return mk(bd, :/, mul(t, d[1]), mul(bd.lift(2), a[1]))
        n === :cbrt && return mk(bd, :/, mul(t, d[1]), mul(bd.lift(3), a[1]))
        n === :exp && return mul(t, d[1])
        n === :log && return mk(bd, :/, d[1], a[1])
        n === :sin && return mul(mk(bd, :cos, a[1]), d[1])
        n === :cos && return neg(mul(mk(bd, :sin, a[1]), d[1]))
        n === :tan && return mul(mk(bd, :+, bd.lift(1), mk(bd, :^, t, bd.lift(2))), d[1])
        n === :atan && return mk(bd, :/, d[1], mk(bd, :+, bd.lift(1), mk(bd, :^, a[1], bd.lift(2))))
        sq(s, t) = mk(bd, :sqrt, mk(bd, :+, bd.lift(s), mk(bd, :*, bd.lift(-s), mk(bd, :^, t, bd.lift(2))))) # √(s - s t²)
        n === :acot && return neg(mk(bd, :/, d[1], mk(bd, :+, bd.lift(1), mk(bd, :^, a[1], bd.lift(2)))))
        n === :asin && return mk(bd, :/, d[1], sq(1, a[1]))
        n === :acos && return neg(mk(bd, :/, d[1], sq(1, a[1])))
        n === :asinh && return mk(bd, :/, d[1], mk(bd, :sqrt, mk(bd, :+, bd.lift(1), mk(bd, :^, a[1], bd.lift(2)))))
        n === :acosh && return mk(bd, :/, d[1], mk(bd, :sqrt, mk(bd, :+, mk(bd, :^, a[1], bd.lift(2)), bd.lift(-1))))
        n === :atanh && return mk(bd, :/, d[1], mk(bd, :+, bd.lift(1), neg(mk(bd, :^, a[1], bd.lift(2)))))
        # asec u = acos(1/u), acsc u = asin(1/u): ∓u′/(u² √(1 - 1/u²))
        n === :asec && return mk(bd, :/, d[1], mul(mk(bd, :^, a[1], bd.lift(2)), sq(1, mk(bd, :/, bd.lift(1), a[1]))))
        n === :acsc && return neg(mk(bd, :/, d[1], mul(mk(bd, :^, a[1], bd.lift(2)), sq(1, mk(bd, :/, bd.lift(1), a[1])))))
        n === :sec && return mul(t, mk(bd, :tan, a[1]), d[1])
        n === :csc && return neg(mul(t, mk(bd, :cot, a[1]), d[1]))
        n === :cot && return neg(mul(mk(bd, :+, bd.lift(1), mk(bd, :^, t, bd.lift(2))), d[1]))
        n === :sinh && return mul(mk(bd, :cosh, a[1]), d[1])
        n === :cosh && return mul(mk(bd, :sinh, a[1]), d[1])
        n === :tanh && return mul(mk(bd, :+, bd.lift(1), neg(mk(bd, :^, t, bd.lift(2)))), d[1])
        n === :coth && return mul(mk(bd, :+, bd.lift(1), neg(mk(bd, :^, t, bd.lift(2)))), d[1])
        n === :sech && return neg(mul(t, mk(bd, :tanh, a[1]), d[1]))
        n === :csch && return neg(mul(t, mk(bd, :coth, a[1]), d[1]))
    end
    throw(RischNotImplemented("no derivative rule for `$n` (u-substitution)"))
end

# the substitution u as a parse hook: `upow(t)` is k when the term t is U^k
function usub_hook(u, xk::String)
    us = string(u)
    rp = radical_parts(u)                                   # u = v^e
    vs, e0 = rp === nothing ? (nothing, Q(0)) : (string(rp[2]), rp[1])
    kx = nothing                                            # u = x^k
    if isnode(u) && opname(operation(u)) === :^ && string(arguments(u)[1]) == xk
        k = leaf_rational(arguments(u)[2])
        (k !== nothing && isone(denominator(k)) && k > 1) && (kx = Int(numerator(k)))
    end
    intk(r) = isone(denominator(r)) ? Int(numerator(r)) : nothing
    # u = exp(w): exp(m w) = U^m for an integer m
    exp_arg(t) = !isnode(t) ? nothing : opname(operation(t)) === :exp ? arguments(t)[1] :
                 (opname(operation(t)) === :^ && is_e_const(arguments(t)[1])) ? arguments(t)[2] : nothing
    ua = exp_arg(u)
    ue = ua === nothing ? nothing : radicand_element(ua, xk)
    function upow(t)
        s = string(t)
        isnode(t) || return s == vs ? intk(inv(e0)) : nothing       # u = x^e: x = U^(1/e)
        s == us && return 1
        if vs !== nothing
            s == vs && return intk(inv(e0))
            r = radical_parts(t)
            (r !== nothing && string(r[2]) == vs) && return intk(r[1] / e0)
        end
        if kx !== nothing && opname(operation(t)) === :^ && string(arguments(t)[1]) == xk
            m = leaf_rational(arguments(t)[2])
            (m !== nothing && isone(denominator(m))) && return intk(Q(m) / kx)
        end
        if ue !== nothing && !iszero(ue) && (ta = exp_arg(t)) !== nothing
            te = radicand_element(ta, xk)
            if te !== nothing
                m = te / ue
                (degree(m.num) == 0 && degree(m.den) == 0) && return intk(m.num.c[1] / m.den.c[1])
            end
        end
        nothing
    end
    only_in_u(t) = upow(t) !== nothing || (isnode(t) ? all(only_in_u, arguments(t)) : string(t) != xk)
    function hook(t, T)
        k = upow(t)
        k === nothing || return sym_const(T, u)^k
        (isnode(t) && depends_on(t, xk) && only_in_u(t)) || return nothing
        sym_const(T, t)                                     # a function of u only: opaque
    end
    hook, upow
end

# subterms of f to try as u (outermost first): not x, not f, not of degree ≤ 1 in x
function usub_candidates(f, xk::String)
    out, seen = Any[], Set{String}()
    function walk(t)
        isnode(t) || return
        s = string(t)
        if !(s in seen) && depends_on(t, xk)
            push!(seen, s)
            e = radicand_element(t, xk)
            (e === nothing || !isone(e.den) || degree(e.num) > 1) && push!(out, t)
        end
        foreach(walk, arguments(t))
    end
    foreach(walk, isnode(f) ? arguments(f) : Any[])
    out
end

function integrate_usub(f, x, u, bd::Builder; build, lift, verify::Bool)
    @nospecialize f x
    xk = string(x)
    du = term_deriv(bd, u, xk)
    r = integrate_usub_trig(f, x, u, du, bd; build = build, lift = lift, verify = verify)   # u = sech v, …
    r === nothing || return r
    hook, upow = usub_hook(u, xk)
    T, el = build_tower(mk(bd, :/, f, du), xk; subst = hook)
    (levelof(T, el) == 0 && isone(el.den) && degree(el.num) == 0) || return nothing
    c = el.num.c[1]
    if is_complex_field(ctype(T))
        c = to_real(c)
        c === nothing && return nothing
    end
    pw(k) = k == 1 ? bd.x : mk(bd, :^, bd.x, bd.lift(k))
    to_x(t) = (k = upow(t); k !== nothing ? pw(k) : isnode(t) ? term_rebuild(bd, t, Any[to_x(s) for s in arguments(t)]) : t)
    # G = c with u ↦ x, done on the generators before c is printed: u's generator prints as x, an opaque
    # function of u (a subterm of f) as that subterm with u ↦ x. Matching u in the printed c instead would
    # depend on how the term type simplifies what is built (SymJ distributes constants over sums).
    consts = ConstGen[g.kind === :sym ? ConstGen(:sym, g.arg, to_x(g.term)) : g for g in T.consts]
    G = cterm(Builder(bd.build, bd.lift, bd.x, consts), c)
    H = risch_integrate(G, x; build = build, lift = lift, verify = verify)
    H isa IntegralWithRootSums && return nothing
    back(t) = isnode(t) ? term_rebuild(bd, t, Any[back(s) for s in arguments(t)]) : (string(t) == xk ? u : t)
    back(H)
end

# the first substitution that works, or nothing
function try_usub(f, x; build, lift, verify::Bool)
    @nospecialize f x
    USUB_DEPTH[] < 2 || return nothing
    xk = string(x)
    bd = Builder(build === nothing ? auto_build(f, x) : build, lift === nothing ? auto_lift(f, x) : lift, x)
    USUB_DEPTH[] += 1
    try
        for u in usub_candidates(f, xk)
            r = try
                integrate_usub(f, x, u, bd; build = build, lift = lift, verify = verify)
            catch e
                (e isa RischNotImplemented || e isa NotElementary) || rethrow()
                nothing
            end
            r === nothing || return r
        end
    finally
        USUB_DEPTH[] -= 1
    end
    nothing
end

# ---------------------------------------------------------------------------
# u-substitution for u = h(v), h a trigonometric or hyperbolic function: f/u′ = c·C^A·S^B with C, S = cos v, sin v
# (cosh v, sinh v), each factor a power (rational exponents allowed) of one of the six functions of v. With
# U = u, C and S are U^p P(U)^(r/2) (sech: C = U⁻¹, S = (1 - U²)^(1/2) U⁻¹); the square-root factor P^(1/2) must
# enter with an integer total power (so no sign of √P is assumed), U to any rational power (U > 0 where
# a fractional power of u is in the integrand already). Then f dx = c U^α P(U)^β dU.
# ---------------------------------------------------------------------------
const TRIG_CS = Dict(:sin => (0, 1), :cos => (1, 0), :tan => (-1, 1), :cot => (1, -1), :sec => (-1, 0), :csc => (0, -1))
const HYP_CS = Dict(:sinh => (0, 1), :cosh => (1, 0), :tanh => (-1, 1), :coth => (1, -1), :sech => (-1, 0), :csch => (0, -1))
# h ↦ (C = U^c1 P^(c2/2), S = U^s1 P^(s2/2)) with P(U) as coefficients (U⁰, U¹, U²)
const CS_OF_U = Dict(
    :cos => ((1, 0), (0, 1), (1, 0, -1)), :sin => ((0, 1), (1, 0), (1, 0, -1)),
    :sec => ((-1, 0), (-1, 1), (-1, 0, 1)), :csc => ((-1, 1), (-1, 0), (-1, 0, 1)),
    :tan => ((0, -1), (1, -1), (1, 0, 1)), :cot => ((1, -1), (0, -1), (1, 0, 1)),
    :cosh => ((1, 0), (0, 1), (-1, 0, 1)), :sinh => ((0, 1), (1, 0), (1, 0, 1)),
    :sech => ((-1, 0), (-1, 1), (1, 0, -1)), :csch => ((-1, 1), (-1, 0), (1, 0, 1)),
    :tanh => ((0, -1), (1, -1), (1, 0, -1)), :coth => ((1, -1), (0, -1), (-1, 0, 1)))

function integrate_usub_trig(f, x, u, du, bd::Builder; build, lift, verify::Bool)
    @nospecialize f x
    xk = string(x)
    (isnode(u) && length(arguments(u)) == 1) || return nothing
    h = opname(operation(u))
    haskey(CS_OF_U, h) || return nothing
    family = haskey(TRIG_CS, h) ? TRIG_CS : HYP_CS
    vs = string(arguments(u)[1])
    A, B = Ref(Q(0)), Ref(Q(0))
    cs = Any[]
    function collect!(t, e::Q)
        if !depends_on(t, xk)
            push!(cs, isone(e) ? t : mk(bd, :^, t, bd.lift(e)))
            return true
        end
        isnode(t) || return false
        n, args = opname(operation(t)), arguments(t)
        n === :* && return all(a -> collect!(a, e), args)
        (n === :/ && length(args) == 2) && return collect!(args[1], e) && collect!(args[2], -e)
        if n === :^ && length(args) == 2
            k = leaf_rational(args[2])
            k === nothing && return false
            return collect!(args[1], e * Q(k))
        end
        n === :sqrt && return collect!(args[1], e / 2)
        if haskey(family, n) && length(args) == 1 && string(args[1]) == vs
            a, b = family[n]
            A[] += e * a
            B[] += e * b
            return true
        end
        false
    end
    collect!(f, Q(1)) && collect!(du, Q(-1)) || return nothing
    (c1, c2), (s1, s2), pc = CS_OF_U[h]
    α = A[] * c1 + B[] * s1                             # C^A S^B = U^α P^(β/2)
    β = A[] * c2 + B[] * s2
    (isone(denominator(β)) && iseven(numerator(β))) || return nothing
    Pt = mk(bd, :+, bd.lift(pc[1]), mk(bd, :*, bd.lift(pc[3]), mk(bd, :^, bd.x, bd.lift(2))))
    fs = Any[cs...]
    iszero(α) || push!(fs, isone(α) ? bd.x : mk(bd, :^, bd.x, bd.lift(α)))
    iszero(β) || push!(fs, mk(bd, :^, Pt, bd.lift(Int(numerator(β)) ÷ 2)))
    G = isempty(fs) ? bd.lift(1) : length(fs) == 1 ? fs[1] : mk(bd, :*, fs...)
    H = risch_integrate(G, x; build = build, lift = lift, verify = verify)
    H isa IntegralWithRootSums && return nothing
    back(t) = isnode(t) ? term_rebuild(bd, t, Any[back(s) for s in arguments(t)]) : (string(t) == xk ? u : t)
    back(H)
end
