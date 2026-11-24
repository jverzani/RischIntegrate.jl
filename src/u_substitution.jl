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
# When v (u = v^(1/m), or u itself, m = 1) is a + b·θ with θ = log(w) or exp(w) and a, b free of θ, θ is
# U^m - a over b wherever it occurs, so v in another form is still seen as U^m (u = √(x + log x) for
# (x + 1)√(x + log x)/(x log² x + 2x² log x + x³), Rubi 220).
# ---------------------------------------------------------------------------

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
        elseif d[1] === nothing                                 # b^w, b free of x: b^w log(b) w′
            return mul(t, mk(bd, :log, a[1]), d[2])
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
        # asin(N/D) or asin(c N) with a factor D = 1/c free of x and not rational (a parameter): N′/√(D² - N²)
        # for D > 0, the radical of the integrand (∫ asin(x/a)^(3/2)/√(a² - x²) by u = asin(x/a)), -N′/√(D² - N²)
        # when the caller's oracle says D < 0 (step SO), and with the factor D/√(D²) when the sign is not known
        # (exact for every real D: x acos(a x²), sample 2345, was wrong for a < 0)
        if n in (:asin, :acos)
            ND = param_quotient(bd, a[1], xk)
            if ND !== nothing
                N, Dd = ND
                r = mk(bd, :/, term_deriv(bd, N, xk), mk(bd, :sqrt, bd.build(-, mk(bd, :^, Dd, bd.lift(2)), mk(bd, :^, N, bd.lift(2)))))
                sD = term_oracle_sign(Dd)
                sD == -1 && (r = neg(r))
                sD === nothing && (r = mk(bd, :*, mk(bd, :/, Dd, mk(bd, :sqrt, mk(bd, :^, Dd, bd.lift(2)))), r))
                return n === :asin ? r : neg(r)
            end
        end
        n === :asin && return mk(bd, :/, d[1], sq(1, a[1]))
        n === :acos && return neg(mk(bd, :/, d[1], sq(1, a[1])))
        n === :asinh && return mk(bd, :/, d[1], mk(bd, :sqrt, mk(bd, :+, bd.lift(1), mk(bd, :^, a[1], bd.lift(2)))))
        n === :acosh && return mk(bd, :/, d[1], mk(bd, :sqrt, mk(bd, :+, mk(bd, :^, a[1], bd.lift(2)), bd.lift(-1))))
        n in (:atanh, :acoth) && return mk(bd, :/, d[1], mk(bd, :+, bd.lift(1), neg(mk(bd, :^, a[1], bd.lift(2)))))
        # asech u = acosh(1/u), 0 < u ≤ 1: -u′/(u √(1 - u²)); acsch u = asinh(1/u): -u′/(u² √(1 + 1/u²))
        n === :asech && return neg(mk(bd, :/, d[1], mul(a[1], sq(1, a[1]))))
        n === :acsch && return neg(mk(bd, :/, d[1], mul(mk(bd, :^, a[1], bd.lift(2)),
                                                        mk(bd, :sqrt, mk(bd, :+, bd.lift(1), mk(bd, :^, a[1], bd.lift(-2)))))))
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
    m = rp === nothing ? 1 : intk(inv(e0))
    lin = m === nothing ? nothing : linear_theta(rp === nothing ? u : rp[2], xk)
    function hook(t, T)
        k = upow(t)
        k === nothing || return sym_const(T, u)^k
        if lin !== nothing && string(t) == lin[1]          # θ = (U^m - a)/b
            r = sym_const(T, u)^m
            for a in lin[2]
                r, ae = unify(T, r, parse_tower(a, T))
                r -= ae
            end
            B = nothing
            for fs in lin[3]
                c = nothing
                for (fa, e) in fs
                    fe = parse_tower(fa, T)^abs(e)
                    c = c === nothing ? (e > 0 ? fe : inv(fe)) : fold_op(T, e > 0 ? (*) : (/), Any[c, fe])
                end
                B = B === nothing ? c : fold_op(T, +, Any[B, c])
            end
            return fold_op(T, /, Any[r, B])
        end
        (isnode(t) && depends_on(t, xk) && only_in_u(t)) || return nothing
        sym_const(T, t)                                     # a function of u only: opaque
    end
    hook, upow
end

# v = a + b·θ, θ = log(w) or exp(w) depending on x, a and b free of θ, not both free of x: (θ's string, the terms of a, the terms of
# b as factor lists [(factor, exponent)]), or nothing
function linear_theta(v, xk::String)
    isnode(v) || return nothing
    ts = opname(operation(v)) === :+ ? arguments(v) : Any[v]
    istheta(t) = isnode(t) && depends_on(t, xk) && (opname(operation(t)) in (:log, :exp) ||
                 (opname(operation(t)) === :^ && is_e_const(arguments(t)[1])))
    cands = Any[]
    walk(t) = (istheta(t) && push!(cands, t); isnode(t) && foreach(walk, arguments(t)))
    walk(v)
    for θ in cands
        θs = string(θ)
        as, bs = Any[], Any[]
        for t in ts
            if !occursin(θs, string(t))
                push!(as, t)
                continue
            end
            fs = product_factors!(Any[], t, 1)
            j = findall(((f, _),) -> string(f) == θs, fs)
            (length(j) == 1 && fs[j[1]][2] == 1) || (bs = nothing; break)
            rest = [fs[i] for i in eachindex(fs) if i != j[1]]
            any(((f, _),) -> occursin(θs, string(f)), rest) && (bs = nothing; break)
            isempty(rest) && (rest = Any[(1, 1)])
            push!(bs, rest)
        end
        (bs === nothing || isempty(bs)) && continue
        # a, b free of x: u = θ covers it (and gives the better answer: ₂F₁ of e^(nx) for (a + b e^(nx))^q)
        (any(t -> depends_on(t, xk), as) || any(fs -> any(((f, _),) -> depends_on(f, xk), fs), bs)) || continue
        return (θs, as, bs)
    end
    nothing
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
    # xᵈ for the divisors d of the powers xⁿ in f (x/√(a⁴ - x⁴): u = x², not a subterm)
    for t in copy(out)
        k = usub_xpower(t, xk)
        k === nothing && continue
        for d in 2:k-1
            k % d == 0 || continue
            v = Expr(:call, :^, Symbol(xk), d)
            string(v) in seen && continue
            push!(seen, string(v))
            push!(out, t isa Expr ? v : arguments(t)[1]^d)
        end
    end
    out
end

function integrate_usub(f, x, u, bd::Builder; build, lift, verify::Bool)
    @nospecialize f x
    xk = string(x)
    du = term_deriv(bd, u, xk)
    # u constant in x though written with x (sin²t + cos²t, whose u′ the term type cancels to 0): not a substitution
    (du === nothing || leaf_rational(du) == 0) && return nothing
    r = integrate_usub_trig(f, x, u, du, bd; build = build, lift = lift, verify = verify)   # u = sech v, …
    r === nothing || return r
    r = integrate_usub_pyth(f, x, u, du, bd; build = build, lift = lift, verify = verify)   # u = sinh v, cosh² = 1 + u²
    r === nothing || return r
    hook, upow = usub_hook(u, xk)
    T, el = build_tower(cancel_quotient(bd, f, du), xk; subst = hook)
    levelof(T, el) == 0 || return nothing
    # u = xᵏ: a rational function of xᵏ (the bare x's of f/u′, 1/(2x·x) for u = x²) is one of U = xᵏ
    k = usub_xpower(u, xk)
    Gx = nothing
    if !(isone(el.den) && degree(el.num) == 0)
        (k !== nothing && is_complex_field(ctype(T)) == false) || return nothing
        ok(p) = all(i -> iszero(p.c[i]) || (i - 1) % k == 0, eachindex(p.c))
        (ok(el.num) && ok(el.den)) || return nothing
        cp(p) = typeof(p)(p.c[1:k:end])
        Gx = frac(cp(el.num), cp(el.den))
    end
    pw(k) = k == 1 ? bd.x : mk(bd, :^, bd.x, bd.lift(k))
    to_x(t) = (k = upow(t); k !== nothing ? pw(k) : isnode(t) ? term_rebuild(bd, t, Any[to_x(s) for s in arguments(t)]) : t)
    if Gx !== nothing
        consts = ConstGen[g.kind === :sym ? ConstGen(:sym, g.arg, to_x(g.term)) : g for g in T.consts]
        G = frac_term(Builder(bd.build, bd.lift, bd.x, consts), Gx)
        H = risch_integrate(G, x; build = build, lift = lift, verify = verify)
        backx(t) = isnode(t) ? term_rebuild(bd, t, Any[backx(s) for s in arguments(t)]) : (string(t) == xk ? u : t)
        return subst_answer(H, backx, bd)
    end
    c = el.num.c[1]
    if is_complex_field(ctype(T))
        c = to_real(c)
        c === nothing && return nothing
    end
    # G = c with u ↦ x, done on the generators before c is printed: u's generator prints as x, an opaque
    # function of u (a subterm of f) as that subterm with u ↦ x. Matching u in the printed c instead would
    # depend on how the term type simplifies what is built (SymJ distributes constants over sums).
    consts = ConstGen[g.kind === :sym ? ConstGen(:sym, g.arg, to_x(g.term)) : g for g in T.consts]
    G = cterm(Builder(bd.build, bd.lift, bd.x, consts), c)
    H = risch_integrate(G, x; build = build, lift = lift, verify = verify)
    back(t) = isnode(t) ? term_rebuild(bd, t, Any[back(s) for s in arguments(t)]) : (string(t) == xk ? u : t)
    subst_answer(H, back, bd)
end

# the first substitution that works, or nothing
function try_usub(f, x; build, lift, verify::Bool)
    @nospecialize f x
    USUB_DEPTH[] < 2 || return nothing
    # (not inside step AP for an integrand with i in it: Q·w′/(1 + w²) from x² atan(c + (1 + ic) tan(bx + a)), SymPy
    # #26509, ran through about a hundred substitutions over ℚ(i)(a, b, c), each refused)
    (PARTS[] && has_imag_unit(f)) && return nothing
    xk = string(x)
    bd = Builder(build === nothing ? auto_build(f, x) : build, lift === nothing ? auto_lift(f, x) : lift, x)
    USUB_DEPTH[] += 1
    # (the Pythagorean partners of sin, cos, sinh, cosh subterms too: u = sinh x for a function of cosh² x times cosh x)
    partner = Dict(:cos => :sin, :sin => :cos, :cosh => :sinh, :sinh => :cosh)
    cands = Any[usub_candidates(f, xk)...]
    seen = Set(string.(cands))
    for t in copy(cands)
        (isnode(t) && length(arguments(t)) == 1 && haskey(partner, opname(operation(t)))) || continue
        p = mk(bd, partner[opname(operation(t))], arguments(t)[1])
        string(p) in seen || (push!(cands, p); push!(seen, string(p)))
    end
    try
        for u in cands
            r = try
                integrate_usub(f, x, u, bd; build = build, lift = lift, verify = verify)
            catch e
                # (DivideError: u′ is zero in the tower where u is opaque, ∫ asech(a x)/x: not a substitution)
                (e isa RischNotImplemented || e isa NotElementary || e isa DivideError) || rethrow()
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
# a fractional power of u is in the integrand already). Then f dx = c U^α P(U)^β dU. A fractional exponent e is
# taken inside only where (∏ tᵢ)^e = ∏ tᵢ^e, (t^k)^e = t^(k e) hold on the principal branch for every x: one
# factor with x, to the first power (√(sin x/cos² x) = √(sin x)/|cos x|, not √(sin x)/cos x, is refused here).
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
        # (under a fractional e: at most one factor with x, not in a denominator)
        nx = count(a -> depends_on(a, xk), args)
        n === :* && return (isinteger(e) || nx <= 1) && all(a -> collect!(a, e), args)
        if n === :/ && length(args) == 2
            (isinteger(e) || !depends_on(args[2], xk)) || return false
            return collect!(args[1], e) && collect!(args[2], -e)
        end
        if n === :^ && length(args) == 2
            k = leaf_rational(args[2])
            k === nothing && return false
            # (t^k)^e = t^(k e) for all t when e is an integer, or k = 1/m (log t^(1/m) = log(t)/m)
            (isinteger(e) || (isone(numerator(Q(k))) && k > 0)) || return false
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
    back(t) = isnode(t) ? term_rebuild(bd, t, Any[back(s) for s in arguments(t)]) : (string(t) == xk ? u : t)
    subst_answer(H, back, bd)
end

# u = h(v), h = sin, cos, sinh, cosh: f/u′ with h(v) ↦ U and the even powers of the companion function written in U
# (cos² v = 1 - U², sin² v = 1 - U², cosh² v = 1 + U², sinh² v = U² - 1), other functions of x left alone only when
# they are free of x (log(1 + cosh²x)² cosh x: u = sinh x, ∫ log(2 + U²)² dU, Rubi 201). Nothing when x remains.
const PYTH = Dict(:sin => (:cos, 1, -1), :cos => (:sin, 1, -1), :sinh => (:cosh, 1, 1), :cosh => (:sinh, -1, 1))
function integrate_usub_pyth(f, x, u, du, bd::Builder; build, lift, verify::Bool)
    @nospecialize f x
    xk = string(x)
    (isnode(u) && length(arguments(u)) == 1) || return nothing
    h = opname(operation(u))
    haskey(PYTH, h) || return nothing
    comp, c0, c2 = PYTH[h]                              # companion² = c0 + c2 U²
    vs = string(arguments(u)[1])
    us = string(u)
    U = bd.x
    sq = mk(bd, :+, bd.lift(c0), mk(bd, :*, bd.lift(c2), mk(bd, :^, U, bd.lift(2))))
    ok = Ref(true)
    iscomp(t) = isnode(t) && opname(operation(t)) === comp && length(arguments(t)) == 1 && string(arguments(t)[1]) == vs
    function walk(t)
        string(t) == us && return U
        if !isnode(t)
            string(t) == xk && (ok[] = false)
            return t
        end
        if opname(operation(t)) === :^ && length(arguments(t)) == 2 && iscomp(arguments(t)[1])
            k = leaf_rational(arguments(t)[2])
            if k !== nothing && isone(denominator(k)) && iseven(numerator(k))
                n = Int(numerator(k)) ÷ 2
                return n == 1 ? sq : mk(bd, :^, sq, bd.lift(n))
            end
        end
        iscomp(t) && (ok[] = false)
        term_rebuild(bd, t, Any[walk(a) for a in arguments(t)])
    end
    g = walk(cancel_quotient(bd, f, du))
    ok[] || return nothing
    H = risch_integrate(g, x; build = build, lift = lift, verify = verify)
    back(t) = isnode(t) ? term_rebuild(bd, t, Any[back(s) for s in arguments(t)]) : (string(t) == xk ? u : t)
    subst_answer(H, back, bd)
end

# k when u = xᵏ (k ≥ 2), else nothing
function usub_xpower(u, xk::String)
    (isnode(u) && opname(operation(u)) === :^ && string(arguments(u)[1]) == xk) || return nothing
    k = leaf_rational(arguments(u)[2])
    (k !== nothing && isone(denominator(k)) && k > 1) ? Int(numerator(k)) : nothing
end

# t = N/D or t = c·N (D = 1/c) with D free of x and not a rational number: (N, D), else nothing
function param_quotient(bd::Builder, t, xk::String)
    isnode(t) || return nothing
    n, args = opname(operation(t)), arguments(t)
    if n === :/ && length(args) == 2 && !depends_on(args[2], xk) && depends_on(args[1], xk)
        return leaf_rational(args[2]) === nothing ? (args[1], args[2]) : nothing
    end
    n === :* || return nothing
    cs = Any[a for a in args if !depends_on(a, xk)]
    ds = Any[a for a in args if depends_on(a, xk)]
    (isempty(cs) || isempty(ds) || all(c -> leaf_rational(c) !== nothing, cs)) && return nothing
    N = length(ds) == 1 ? ds[1] : mk(bd, :*, ds...)
    c = length(cs) == 1 ? cs[1] : mk(bd, :*, cs...)
    (N, mk(bd, :/, bd.lift(1), c))
end

# f/g with the factors common to both (the same printed term, or radicals of the same rational radicand:
# √(x² + 1) and √(1 + x²)) cancelled: a radical of the integrand that is also in u′ (√(a² - x²) for u = asin(x/a))
# does not reach the tower, which has no algebraic generators here
function cancel_quotient(bd::Builder, f, g)
    leaf_rational(g) == 0 && throw(RischNotImplemented("division by a zero derivative"))
    fs, gs = product_factors!(Any[], f, 1), product_factors!(Any[], g, 1)
    xk = string(bd.x)
    function key(t)
        rp = radical_parts(t)
        rp === nothing && return string(t)
        ue = radicand_element(rp[2], xk)
        ue === nothing ? string(t) : string("radical ", rp[1], " of ", ue)
    end
    ex = Dict{String,Tuple{Any,Int}}()
    for (t, e) in fs
        k = key(t)
        ex[k] = (t, get(ex, k, (t, 0))[2] + e)
    end
    for (t, e) in gs
        k = key(t)
        ex[k] = (t, get(ex, k, (t, 0))[2] - e)
    end
    gk = Set(key(s) for (s, _) in gs)
    any(((t, _),) -> key(t) in gk, fs) || return mk(bd, :/, f, g)
    num, den = Any[], Any[]
    for (t, e) in values(ex)
        e == 0 && continue
        push!(e > 0 ? num : den, abs(e) == 1 ? t : mk(bd, :^, t, bd.lift(abs(e))))
    end
    pr(v) = isempty(v) ? bd.lift(1) : length(v) == 1 ? v[1] : mk(bd, :*, v...)
    isempty(den) ? pr(num) : mk(bd, :/, pr(num), pr(den))
end

# ---------------------------------------------------------------------------
# Step CB: Chebyshev's binomials and their kin, f = C x^m h(xⁿ) (x^m from factors x^r and (c x)^r = c^r x^r, for c, x > 0;
# every other x in f inside a power x^k with n | k, n ≥ 2): u = xⁿ, ∫ f dx = (1/n) ∫ C u^((m+1)/n - 1) h(u) du, then
# u ↦ xⁿ. √x/(1 - x²)^(3/4) becomes u^(-1/4) (1 - u)^(-3/4)/2, one Möbius radicand ((1 - u)/u)^(1/4) (Rubi 1.1.3:
# (c x)^(1/2)/(a - b x²)^(3/4), x⁸/(a - b x⁴)^(1/4)). After a radical refusal, in the outermost call.
# ---------------------------------------------------------------------------
function integrate_monomial_power_subst(f, x; build = nothing, lift = nothing, verify::Bool = true)
    @nospecialize f x
    xk = string(x)
    isx(t) = !isnode(t) && string(t) == xk
    bd = Builder(build === nothing ? auto_build(f, x) : build, lift === nothing ? auto_lift(f, x) : lift, x)
    # c x (c free of x): c, else nothing
    function cx(t)
        isx(t) && return bd.lift(1)
        (isnode(t) && opname(operation(t)) === :* ) || return nothing
        as = arguments(t)
        js = findall(isx, as)
        (length(js) == 1 && all(a -> isx(a) || !depends_on(a, xk), as)) || return nothing
        rest = Any[a for (j, a) in enumerate(as) if j != js[1]]
        length(rest) == 1 ? rest[1] : mk(bd, :*, rest...)
    end
    # the exponents k of the powers x^k in t (bare x: 1)
    function xexps!(t, acc)
        isx(t) && return push!(acc, 1)
        isnode(t) || return acc
        if opname(operation(t)) === :^ && length(arguments(t)) == 2 && isx(arguments(t)[1])
            k = leaf_rational(arguments(t)[2])
            return push!(acc, k === nothing || !isone(denominator(k)) ? 0 : Int(numerator(k)))
        end
        foreach(a -> xexps!(a, acc), arguments(t))
        acc
    end
    m = Q(0)
    consts, others = Any[], Any[]
    for (t, e) in product_factors!(Any[], f, 1)
        base, r = t, Q(e)
        if isnode(t) && opname(operation(t)) === :^ && length(arguments(t)) == 2 && leaf_rational(arguments(t)[2]) !== nothing
            base, r = arguments(t)[1], Q(leaf_rational(arguments(t)[2])) * e
        elseif isnode(t) && opname(operation(t)) === :sqrt
            base, r = arguments(t)[1], Q(e) / 2
        end
        if !depends_on(t, xk)
            push!(consts, e == 1 ? t : mk(bd, :^, t, bd.lift(e)))
        elseif (c = cx(base)) !== nothing
            m += r
            string(c) == "1" || push!(consts, mk(bd, :^, c, bd.lift(r)))
        else
            push!(others, e == 1 ? t : mk(bd, :^, t, bd.lift(e)))
        end
    end
    isempty(others) && return nothing
    ks = reduce(vcat, [collect(xexps!(t, Int[])) for t in others])
    (isempty(ks) || any(iszero, ks)) && return nothing
    n = reduce(gcd, ks)
    n >= 2 || return nothing
    # x^k ↦ x^(k/n) in the others (x now standing for u)
    function down(t)
        isnode(t) || return t
        if opname(operation(t)) === :^ && length(arguments(t)) == 2 && isx(arguments(t)[1])
            k = Int(leaf_rational(arguments(t)[2])) ÷ n
            return k == 1 ? bd.x : mk(bd, :^, bd.x, bd.lift(k))
        end
        term_rebuild(bd, t, Any[down(a) for a in arguments(t)])
    end
    q = (m + 1) / n - 1
    g = Any[bd.lift(Q(1, n)), consts..., (down(t) for t in others)...]
    iszero(q) || push!(g, mk(bd, :^, bd.x, bd.lift(q)))
    G = try
        risch_integrate(mk(bd, :*, g...), x; build = build, lift = lift, verify = verify)
    catch e
        (e isa RischNotImplemented || e isa NotElementary) || rethrow()
        return nothing
    end
    xn = mk(bd, :^, bd.x, bd.lift(n))
    back0(t) = isnode(t) ? term_rebuild(bd, t, Any[back0(a) for a in arguments(t)]) : (isx(t) ? xn : t)
    # u = xⁿ put back, the answer's radicals with powers of x in the radicand as real roots: (Q x^k)^e = Q^e x^(k e)
    # for an integer k e ((x³)^(1/3) = x, ((a + b x³)/x³)^(1/3) = (a + b x³)^(1/3)/x). These radicals are not the
    # integrand's: any root, the same everywhere, keeps F′ = f (an identity in the radicals with rᵠ = R and
    # r′ = e r R′/R; the factors σ = r₁ r₂/r₃ of steps LL, RM are then exact ratios of those roots). The principal
    # ones are not real for x < 0 with n odd, where the integral in u, for u > 0, does not continue (sample 613,
    # x³ (a + b x³)^(2/3)/(c + d x³), at a + b x³ > 0, x < 0)
    function realroots(t)
        isnode(t) || return t
        t = term_rebuild(bd, t, Any[realroots(a) for a in arguments(t)])
        rp = radical_parts(t)
        (rp === nothing || !depends_on(rp[2], xk)) && return t
        e, R = rp
        k, rest = Q(0), Any[]
        for (s, j) in product_factors!(Any[], R, 1)
            if isx(s)
                k += j
            elseif isnode(s) && opname(operation(s)) === :^ && length(arguments(s)) == 2 && isx(arguments(s)[1]) &&
                   (p = leaf_rational(arguments(s)[2]); p !== nothing && isone(denominator(p)))
                k += Int(p) * j
            else
                push!(rest, j == 1 ? s : mk(bd, :^, s, bd.lift(j)))
            end
        end
        (iszero(k) || !isone(denominator(k * e))) && return t
        xk_ = Int(k * e)
        xp = xk_ == 1 ? bd.x : mk(bd, :^, bd.x, bd.lift(xk_))
        isempty(rest) && return xp
        Rr = length(rest) == 1 ? rest[1] : mk(bd, :*, rest...)
        mk(bd, :*, e == Q(1) // 2 ? mk(bd, :sqrt, Rr) : mk(bd, :^, Rr, bd.lift(e)), xp)
    end
    back(t) = realroots(back0(t))
    subst_answer(G, back, bd)
end

# ---------------------------------------------------------------------------
# Step HB: Bioche's rules for hyperbolic functions, the odd cases. f with parameters, its x only inside hyperbolic
# functions of one argument L: u = cosh L (f = sinh L · g(cosh L), with sinh² L = u² - 1) or u = sinh L, by
# derivative-divides (`integrate_usub`, exact), before the route through e^L, whose degree in e^L doubles the
# quartic: sinh(c + d x)⁹/(a - b sinh(c + d x)⁴)², sample 2496, ran for minutes there and takes a second in u. Nothing
# when f is not of this kind (the trigonometric cases are step TS's, in θ = e^(iL)).
# ---------------------------------------------------------------------------
const HYP_FUNS = (:sinh, :cosh, :tanh, :coth, :sech, :csch)
function integrate_hyp_bioche(f, x; build, lift, verify::Bool)
    @nospecialize f x
    xk = string(x)
    (USUB_DEPTH[] < 2 && has_param_not_i(f, xk)) || return nothing
    L = nothing
    function walk(t)
        (safe_iscall(t) && !isempty(arguments(t))) || return string(t) != xk     # (x only inside the functions)
        n = opname(operation(t))
        if n in HYP_FUNS && length(arguments(t)) == 1 && has_x(arguments(t)[1], xk)
            a = arguments(t)[1]
            L === nothing && (L = a)
            return string(a) == string(L)
        end
        (n in (:+, :-, :*, :/, :^, :sqrt) || !has_x(t, xk)) || return false
        all(walk, arguments(t))
    end
    (walk(f) && L !== nothing) || return nothing
    pp = poly_parts(Builder(build === nothing ? auto_build(f, x) : build, lift === nothing ? auto_lift(f, x) : lift, x), L, xk)
    (pp === nothing || maximum(keys(pp)) != 1) && return nothing       # (L linear in x)
    bd = Builder(build === nothing ? auto_build(f, x) : build, lift === nothing ? auto_lift(f, x) : lift, x)
    USUB_DEPTH[] += 1
    try
        for h in (:cosh, :sinh)
            r = try
                integrate_usub(f, x, mk(bd, h, L), bd; build = build, lift = lift, verify = verify)
            catch e
                (e isa RischNotImplemented || e isa NotElementary || e isa DivideError) || rethrow()
                nothing
            end
            r === nothing || return r
        end
        # u = tanh L or coth L, the other written as 1/u (coth³/√(a + b tanh²), sample 2570; coth (a + b coth²)^(3/2), 2588:
        # a radical of a rational function of u, which the radical steps take)
        hs = ((:tanh, :coth), (:coth, :tanh))         # (the one in f first: coth for 2588, no 1/tanh in the answer)
        hasf(t, n) = isnode(t) && ((opname(operation(t)) === n && string(arguments(t)[1]) == string(L)) || any(a -> hasf(a, n), arguments(t)))
        (hasf(f, :coth) && !hasf(f, :tanh)) && (hs = reverse(hs))
        for (h, o) in hs
            Ls = string(L)
            recip(t) = isnode(t) ? (opname(operation(t)) === o && length(arguments(t)) == 1 && string(arguments(t)[1]) == Ls ?
                                    mk(bd, :/, bd.lift(1), mk(bd, h, L)) : term_rebuild(bd, t, Any[recip(a) for a in arguments(t)])) : t
            r = try
                integrate_usub(recip(f), x, mk(bd, h, L), bd; build = build, lift = lift, verify = verify)
            catch e
                (e isa RischNotImplemented || e isa NotElementary || e isa DivideError) || rethrow()
                nothing
            end
            r === nothing || return r
        end
    finally
        USUB_DEPTH[] -= 1
    end
    nothing
end

# step GU: u = x/√R for an even quartic R = a + b x² + c x⁴ (a, c ≠ 0), Goursat's substitution for pseudo-elliptic
# integrands: u′ = (a - c x⁴)/R^(3/2), and a rational function of t = x² that is unchanged by t ↦ a/(c t) is one of
# u² = t/R. With f/u′ = N(t)/D(t) (√R written S, f S³/(a - c x⁴) even in S, S² = R), N and D reduced modulo
# Q(t) = c u² t² + (b u² - 1) t + a u² (whose roots are the two t of one u) leave n₁ t + n₀ and d₁ t + d₀,
# proportional when f/u′ is a function of u: then f dx = W(u) du, W = n₁/d₁ (or n₀/d₀). √(a + b x² + c x⁴)/(a - c x⁴)
# is 1/((1 - b u²)² - 4 a c u⁴) (sample 1036: over the parameters, the hyperelliptic log part's torsion search, done
# modulo primes, does not apply). Expr in and out; nothing when f is not so
function goursat_quartic_expr(f, xs::Symbol; verify::Bool = true)
    xk = string(xs)
    rads = collect_radicals(f, xk)
    isempty(rads) && return nothing
    R = rads[1][2]
    all(((e, v),) -> denominator(e) == 2 && v == R, rads) || return nothing
    tw(t, v) = try
        build_tower(t, v)
    catch e
        (e isa RischNotImplemented || e isa RischError || e isa DivideError) || rethrow()
        (nothing, nothing)
    end
    TR, eR = tw(R, xk)
    (TR !== nothing && isempty(TR.levels) && isone(eR.den) && degree(eR.num) == 4) || return nothing
    cR = eR.num.c
    (iszero(cR[2]) && iszero(cR[4]) && !iszero(cR[1]) && !iszero(cR[5])) || return nothing
    bR = Builder(expr_build, identity, xs, TR.consts)
    A, B, C = cterm(bR, cR[1]), cterm(bR, cR[3]), cterm(bR, cR[5])
    S = gensym("S")
    function srad(t)
        t isa Expr || return t
        rp = radical_parts(t)
        (rp !== nothing && rp[2] == R) && return Expr(:call, :^, S, Int(2 * rp[1]))
        Expr(t.head, map(srad, t.args)...)
    end
    # f/u′ in S, then S² = R: a rational function of x
    TS, eS = tw(:($(srad(f)) * $S ^ 3 / ($A - $C * $xs ^ 4)), string(S))
    (TS !== nothing && isempty(TS.levels)) || return nothing
    bS = Builder(expr_build, identity, S, TS.consts)
    function sq(p)
        all(i -> iszero(p.c[i]) || isodd(i), eachindex(p.c)) || return nothing
        Expr(:call, :+, 0, (:($(cterm(bS, p.c[i])) * $R ^ $((i - 1) ÷ 2)) for i in 1:2:length(p.c) if !iszero(p.c[i]))...)
    end
    nw, dw = sq(eS.num), sq(eS.den)
    (nw === nothing || dw === nothing) && return nothing
    T, el = tw(:($nw / $dw), xk)
    (T !== nothing && isempty(T.levels) && !is_complex_field(ctype(T))) || return nothing
    even(p) = all(i -> iszero(p.c[i]) || isodd(i), eachindex(p.c))
    (even(el.num) && even(el.den)) || return nothing
    b = Builder(expr_build, identity, xs, T.consts)
    # coefficients of t⁰, t¹, … (x standing for u), then the remainder modulo Q
    tco(p) = Any[cterm(b, p.c[i]) for i in 1:2:length(p.c)]
    q0, q1, q2 = :($A * $xs ^ 2), :($B * $xs ^ 2 - 1), :($C * $xs ^ 2)
    function remq(cs)
        cs = copy(cs)
        for k in length(cs):-1:3
            m = :($(cs[k]) / $q2)
            cs[k-1] = :($(cs[k-1]) - $m * $q1)
            cs[k-2] = :($(cs[k-2]) - $m * $q0)
        end
        length(cs) == 1 ? (cs[1], 0) : (cs[1], cs[2])
    end
    function iszero_t(t)
        Tz, ez = tw(t, xk)
        Tz !== nothing && isempty(Tz.levels) && iszero(ez.num)
    end
    (n0, n1), (d0, d1) = remq(tco(el.num)), remq(tco(el.den))
    iszero_t(:($n1 * $d0 - $n0 * $d1)) || return nothing
    W = iszero_t(d1) ? :($n0 / $d0) : :($n1 / $d1)
    USUB_DEPTH[] += 1
    H = try
        risch_integrate(W, xs; build = expr_build, lift = identity, verify = verify)
    catch e
        (e isa RischNotImplemented || e isa NotElementary) || rethrow()
        nothing
    finally
        USUB_DEPTH[] -= 1
    end
    (H === nothing || H isa IntegralWithRootSums) && return nothing
    u = :($xs / sqrt($R))
    back(t) = t === xs ? u : t isa Expr ? Expr(t.head, map(back, t.args)...) : t
    back(H)
end

integrate_quartic_goursat(f, x; build = nothing, lift = nothing, verify::Bool = true) = USUB_DEPTH[] < 2 ?
    integrate_rewritten_expr(f, x, (fe, xs) -> nothing, GU_ACTIVE; build = build, lift = lift, verify = verify,
                             answer = (fe, xs) -> goursat_quartic_expr(fe, xs; verify = verify)) : nothing

# t with each symbol that is a key of `d` replaced by its value
subst_symbols(t, d::AbstractDict) = t isa Symbol ? get(d, t, t) : t isa Expr ? Expr(t.head, (subst_symbols(a, d) for a in t.args)...) : t

# step XK in every occurrence: each (c V)^s of f (s free of x and not a number, c the factors of its base free of x)
# is κ V^s, κ a new symbol standing for the constant (c V)^s/V^s. Step XK takes such a power as a factor of f only;
# (c xⁿ)^(1/n) (a + b (c xⁿ)^(1/n)) has one inside a sum (sample 573). An elementary answer only (κ is not real for
# c < 0, and a RootSum with a complex coefficient is evaluated as its real part). Expr in and out; nothing when f
# has no such power
function power_content_expr(f, xs::Symbol; verify::Bool = true)
    xk = string(xs)
    κs, Ks = Dict{Any,Symbol}(), Dict{Symbol,Any}()
    pw(t, k) = k == 1 ? t : Expr(:call, :^, t, k)
    function rw(e)
        e isa Expr || return e
        args = Any[rw(a) for a in e.args]
        if e.head === :call && args[1] === :^ && length(args) == 3
            B, s = args[2], args[3]
            if !has_x(s, xk) && leaf_rational(s) === nothing && has_x(B, xk)
                bfs = product_factors!(Any[], B, 1)
                vs = [pw(u, j) for (u, j) in bfs if has_x(u, xk)]
                if length(vs) < length(bfs) && !isempty(vs)
                    V = length(vs) == 1 ? vs[1] : Expr(:call, :*, vs...)
                    Vs = Expr(:call, :^, V, s)
                    κ = get!(() -> gensym("κ"), κs, (B, s))
                    Ks[κ] = Expr(:call, :/, Expr(:call, :^, B, s), Vs)
                    return Expr(:call, :*, κ, Vs)
                end
            end
        end
        Expr(e.head, args...)
    end
    g = rw(f)
    isempty(Ks) && return nothing
    G = try
        risch_integrate(g, xs; build = expr_build, lift = identity, verify = verify)
    catch e
        (e isa RischNotImplemented || e isa NotElementary) || rethrow()
        nothing
    end
    (G === nothing || G isa IntegralWithRootSums) && return nothing
    subst_symbols(G, Ks)
end

integrate_power_content(f, x; build = nothing, lift = nothing, verify::Bool = true) =
    integrate_rewritten_expr(f, x, (fe, xs) -> nothing, KP_ACTIVE; build = build, lift = lift, verify = verify,
                             answer = (fe, xs) -> power_content_expr(fe, xs; verify = verify))

# step QS: f = h/Q, Q = a + b x + c x² with parameters in its coefficients, by partial fractions over its roots:
# 1/Q = (1/(x - r₁) - 1/(x - r₂))/√(b² - 4ac). ∫ h/(x - ρ) for a new symbol ρ holds for every ρ, so one integral
# P(ρ) gives (P(r₁) - P(r₂))/√(b² - 4ac). Over the parameters the field lacks the roots, and the rational function
# that √(p + q x)/((d + e x)^(3/2) Q) becomes is beyond the residues of a quartic over 6 symbols (sample 905). An
# elementary answer only, for radicals of linear radicands; Expr in and out; nothing when f is not so
function quadratic_split_expr(f, xs::Symbol; verify::Bool = true)
    xk = string(xs)
    fs = product_factors!(Any[], f, 1)
    tw(t) = try
        build_tower(t, xk)
    catch e
        (e isa RischNotImplemented || e isa RischError || e isa DivideError) || rethrow()
        (nothing, nothing)
    end
    iq, T, el = 0, nothing, nothing
    for (i, (t, k)) in enumerate(fs)
        (k == -1 && has_x(t, xk) && has_param(t, xk) && count(u -> u[1] == t, fs) == 1) || continue
        T, el = tw(t)
        if T !== nothing && isempty(T.levels) && isone(el.den) && degree(el.num) == 2
            iq = i
            break
        end
    end
    iq == 0 && return nothing
    # (radicals of linear radicands only, rational after a substitution: a quadratic √(a + c x²) keeps its RootSum
    # route, 1/((d + e x + f x²) √(a + c x²)))
    for (_, v) in collect_radicals(f, xk)
        Tv, ev = tw(v)
        (Tv !== nothing && isempty(Tv.levels) && isone(ev.den) && degree(ev.num) <= 1) || return nothing
    end
    b = Builder(expr_build, identity, xs, T.consts)
    A, B, C = (cterm(b, c) for c in el.num.c)
    b0 = iszero(el.num.c[2])
    Δ = b0 ? :(-4 * $A * $C) : :($B ^ 2 - 4 * $A * $C)
    TΔ, eΔ = tw(Δ)
    (TΔ === nothing || iszero(eΔ.num)) && return nothing
    hs = Any[k == 1 ? t : Expr(:call, :^, t, k) for (i, (t, k)) in enumerate(fs) if i != iq]
    h = isempty(hs) ? 1 : length(hs) == 1 ? hs[1] : Expr(:call, :*, hs...)
    ρ = gensym("ρ")
    P = try
        risch_integrate(:($h / ($xs - $ρ)), xs; build = expr_build, lift = identity, verify = verify)
    catch e
        (e isa RischNotImplemented || e isa NotElementary) || rethrow()
        nothing
    end
    (P === nothing || P isa IntegralWithRootSums) && return nothing
    D = :(sqrt($Δ))
    r1, r2 = b0 ? (:($D / (2 * $C)), :(-$D / (2 * $C))) : (:((-$B + $D) / (2 * $C)), :((-$B - $D) / (2 * $C)))
    :(($(subst_symbols(P, Dict(ρ => r1))) - $(subst_symbols(P, Dict(ρ => r2)))) / $D)
end

integrate_quadratic_split(f, x; build = nothing, lift = nothing, verify::Bool = true) =
    integrate_rewritten_expr(f, x, (fe, xs) -> nothing, QS_ACTIVE; build = build, lift = lift, verify = verify,
                             answer = (fe, xs) -> quadratic_split_expr(fe, xs; verify = verify))

# step LK: A + B log(c Π Vⱼ^kⱼ), with A, B, c, kⱼ free of x and the Vⱼ not, is K + B Σ kⱼ log Vⱼ, K a new symbol
# standing for the constant A + B log(c Π Vⱼ^kⱼ) - B Σ kⱼ log Vⱼ (a bare log with c ≠ 1 the same, A = 0, B = 1).
# A, B, c and the constant the tower makes for log(c Π Vⱼ^kⱼ) - Σ kⱼ log Vⱼ are then one: (A + B log(e ((a + b x)/
# (c + d x))^n))² over g³ i² was refused with 9 constants (samples 1231-1233). Taken on the refusal "more than N
# transcendental constants" only. An elementary answer only. Expr in and out; nothing when f has no such log
function log_content_expr(f, xs::Symbol; verify::Bool = true)
    xk = string(xs)
    hx(t) = has_x(t, xk)
    # log(u) as (constant factors, [(Vⱼ, kⱼ)]): products, quotients and powers with exponents free of x split
    function lsplit!(cs, vs, u, k)
        if u isa Expr && u.head === :call
            op = u.args[1]
            if op === :* 
                foreach(a -> lsplit!(cs, vs, a, k), u.args[2:end])
                return
            elseif op === :/ && length(u.args) == 3
                lsplit!(cs, vs, u.args[2], k)
                lsplit!(cs, vs, u.args[3], k === 1 ? -1 : :(-$k))
                return
            elseif op === :^ && length(u.args) == 3 && !hx(u.args[3]) && hx(u.args[2])
                lsplit!(cs, vs, u.args[2], k === 1 ? u.args[3] : :($k * $(u.args[3])))
                return
            end
        end
        hx(u) ? push!(vs, (u, k)) : push!(cs, (u, k))
    end
    islog(t) = t isa Expr && t.head === :call && t.args[1] === :log && length(t.args) == 2 && hx(t.args[2])
    Ks = Dict{Symbol,Any}()
    # B log(u) → (B, log(u)) when B is free of x
    function coeflog(t)
        islog(t) && return (1, t)
        if t isa Expr && t.head === :call && t.args[1] === :* 
            ls = [a for a in t.args[2:end] if islog(a)]
            (length(ls) == 1 && all(a -> a === ls[1] || !hx(a), t.args[2:end])) || return nothing
            bs = [a for a in t.args[2:end] if a !== ls[1]]
            return (length(bs) == 1 ? bs[1] : Expr(:call, :*, bs...), ls[1])
        end
        nothing
    end
    # A + B log(u) → K + B Σ kⱼ log Vⱼ, or nothing when there is nothing to merge
    function merge(A, B, L)
        cs, vs = Any[], Any[]
        lsplit!(cs, vs, L.args[2], 1)
        (A === nothing && isempty(cs)) && return nothing
        isempty(vs) && return nothing
        K = gensym("K")
        lv = Any[k === 1 ? :(log($V)) : :($k * log($V)) for (V, k) in vs]
        S = length(lv) == 1 ? lv[1] : Expr(:call, :+, lv...)
        BS = B === 1 ? S : :($B * $S)
        Ks[K] = A === nothing ? :($L - $S) : :($A + $B * $L - $BS)
        :($K + $BS)
    end
    function rw(e)
        e isa Expr || return e
        if e.head === :call && e.args[1] === :+
            args = e.args[2:end]
            cl = [coeflog(a) for a in args]
            il = findall(c -> c !== nothing, cl)
            if length(il) == 1 && all(i -> i == il[1] || !hx(args[i]), eachindex(args))
                rest = [args[i] for i in eachindex(args) if i != il[1]]
                A = isempty(rest) ? nothing : length(rest) == 1 ? rest[1] : Expr(:call, :+, rest...)
                B, L = cl[il[1]]
                m = merge(A, B, L)
                m === nothing || return m
            end
        end
        if islog(e)
            m = merge(nothing, 1, e)
            m === nothing || return m
        end
        Expr(e.head, Any[rw(a) for a in e.args]...)
    end
    g = rw(f)
    # the x-free content of each factor, (a g + b g x)³ = g³ (a + b x)³, and the constant factor outside the integral;
    # with a symbolic power s, (h x)^m = K x^m and (a g + b g x)^m = K (a + b x)^m, K = B^s/V^s (as in step XK)
    cs, hs = Any[], Any[]
    split = !isempty(Ks)
    for (t, k) in product_factors!(Any[], g, 1)
        if !hx(t)
            push!(cs, k == 1 ? t : :($t ^ $k))
            continue
        end
        if t isa Expr && t.head === :call && t.args[1] === :^ && length(t.args) == 3 && !hx(t.args[3]) &&
           leaf_rational(t.args[3]) === nothing
            B, sp = t.args[2], t.args[3]
            c, V = sum_symbol_content(B, xk)
            if c === nothing
                bfs = product_factors!(Any[], B, 1)
                vs = [j == 1 ? u : :($u ^ $j) for (u, j) in bfs if hx(u)]
                if length(vs) < length(bfs)
                    c, V = true, length(vs) == 1 ? vs[1] : Expr(:call, :*, vs...)
                end
            end
            if c !== nothing
                Vs = :($V ^ $sp)
                push!(cs, k == 1 ? :($t / $Vs) : :(($t / $Vs) ^ $k))
                push!(hs, k == 1 ? Vs : :($Vs ^ $k))
                split = true
                continue
            end
        end
        c, t = sum_symbol_content(t, xk)
        c === nothing || (push!(cs, k == 1 ? c : :($c ^ $k)); split = true)
        push!(hs, k == 1 ? t : :($t ^ $k))
    end
    split || return nothing
    h = isempty(hs) ? 1 : length(hs) == 1 ? hs[1] : Expr(:call, :*, hs...)
    G = try
        risch_integrate(h, xs; build = expr_build, lift = identity, verify = verify)
    catch e
        (e isa RischNotImplemented || e isa NotElementary) || rethrow()
        nothing
    end
    (G === nothing || G isa IntegralWithRootSums) && return nothing
    G = subst_symbols(G, Ks)
    isempty(cs) ? G : Expr(:call, :*, cs..., G)
end

# (c, s/c) for a sum s whose summands have the symbols c (free of x, to integer powers) as common factors, else
# (nothing, s): a g + b g x = g (a + b x)
function sum_symbol_content(s, xk::String)
    (s isa Expr && s.head === :call && s.args[1] === :+) || return (nothing, s)
    fss = [product_factors!(Any[], a, 1) for a in s.args[2:end]]
    syms(fs) = Dict{Symbol,Int}(t => k for (t, k) in fs if t isa Symbol && string(t) != xk && k > 0)
    com = syms(fss[1])
    for fs in fss[2:end]
        d = syms(fs)
        for (t, k) in collect(com)
            haskey(d, t) ? (com[t] = min(k, d[t])) : delete!(com, t)
        end
    end
    isempty(com) && return (nothing, s)
    function strip(fs)
        left = copy(com)
        out = Any[]
        for (t, k) in fs
            if t isa Symbol && haskey(left, t)
                k -= left[t]
                delete!(left, t)
            end
            k == 0 || push!(out, k == 1 ? t : :($t ^ $k))
        end
        isempty(out) ? 1 : length(out) == 1 ? out[1] : Expr(:call, :*, out...)
    end
    c = [k == 1 ? t : :($t ^ $k) for (t, k) in com]
    (length(c) == 1 ? c[1] : Expr(:call, :*, c...), Expr(:call, :+, map(strip, fss)...))
end

integrate_log_content(f, x; build = nothing, lift = nothing, verify::Bool = true) =
    integrate_rewritten_expr(f, x, (fe, xs) -> nothing, LK_ACTIVE; build = build, lift = lift, verify = verify,
                             answer = (fe, xs) -> log_content_expr(fe, xs; verify = verify))

# step TZ: sin, cos of one argument a + b log(c xⁿ) (a, b, c, n free of x) with b n = i r, r rational. Then
# e^(i(a + b log(c xⁿ))) = E x^(-r), E = e^(i(a + b log(c xⁿ))) x^r constant on intervals, and sin, cos are
# (E x^(-r) ∓ x^r/E)/(2i), (…)/2: powers of x. A square root √(-q²) in b (q rational in the parameters) is σ i q with
# σ = ±1 locally constant: both signs are integrated and the answers joined as ((1 + σ) F₊ + (1 - σ) F₋)/2 with
# σ = √(-q²)/(i q). Over the field the opaque √(-1/(4n²)) of sin(a + √(-1/(4n²)) log(c xⁿ))² left a denominator
# 1 + 4n² s² that vanishes identically (samples 2228, 2230, 2232). Expr in and out; nothing when f is not so
function trig_log_imag_expr(f, xs::Symbol; verify::Bool = true)
    xk = string(xs)
    hx(t) = has_x(t, xk)
    I = :(sqrt(-1))
    args = Any[]
    function scan(t)
        t isa Expr || return
        if t.head === :call && t.args[1] in (:sin, :cos) && length(t.args) == 2 && hx(t.args[2])
            push!(args, t.args[2])
            return
        end
        foreach(scan, t.args)
    end
    scan(f)
    (isempty(args) && return nothing)
    all(==(args[1]), args) || return nothing
    arg = args[1]
    # arg = A + B log(L), L = c x^k
    terms = (arg isa Expr && arg.head === :call && arg.args[1] === :+) ? arg.args[2:end] : Any[arg]
    il = findall(hx, terms)
    length(il) == 1 || return nothing
    bl = terms[il[1]]
    fs = (bl isa Expr && bl.head === :call && bl.args[1] === :*) ? bl.args[2:end] : Any[bl]
    lg = findall(t -> t isa Expr && t.head === :call && t.args[1] === :log && length(t.args) == 2, fs)
    (length(lg) == 1 && all(i -> i == lg[1] || !hx(fs[i]), eachindex(fs))) || return nothing
    L = fs[lg[1]].args[2]
    B = length(fs) == 1 ? 1 : length(fs) == 2 ? fs[3 - lg[1]] : Expr(:call, :*, fs[setdiff(eachindex(fs), lg)]...)
    # L = c x^k
    k = nothing
    for u in ((L isa Expr && L.head === :call && L.args[1] === :*) ? L.args[2:end] : Any[L])
        hx(u) || continue
        k === nothing || return nothing
        if u === xs
            k = 1
        elseif u isa Expr && u.head === :call && u.args[1] === :^ && u.args[2] === xs && !hx(u.args[3])
            k = u.args[3]
        else
            return nothing
        end
    end
    k === nothing && return nothing
    tw(t) = try
        build_tower(t, xk)
    catch e
        (e isa RischNotImplemented || e isa RischError || e isa DivideError) || rethrow()
        (nothing, nothing)
    end
    # the square roots √(-q²) in B
    sq = Dict{Any,Any}()
    function findsq(t)
        t isa Expr || return
        if t.head === :call && t.args[1] === :sqrt && length(t.args) == 2 && !hx(t) && !is_imag_unit(t)
            T, el = tw(:(-($(t.args[2]))))
            if T !== nothing && isempty(T.levels) && degree(el.num) == 0 && degree(el.den) == 0
                q = csqrt(el.num.c[1] / el.den.c[1])
                q === nothing || (sq[t] = cterm(Builder(expr_build, identity, xs, T.consts), q))
            end
            return
        end
        foreach(findsq, t.args)
    end
    findsq(B)
    length(sq) <= 1 || return nothing
    sub(t, d) = haskey(d, t) ? d[t] : t isa Expr ? Expr(t.head, Any[sub(a, d) for a in t.args]...) : t
    function branch(σ)
        Bσ = isempty(sq) ? B : sub(B, Dict(s => :($σ * $I * $q) for (s, q) in sq))
        T, el = tw(:($Bσ * $k))
        (T === nothing || !isempty(T.levels) || degree(el.num) != 0 || degree(el.den) != 0) && return nothing
        v = el.num.c[1] / el.den.c[1]                     # b n = i r
        r = rational_const(-(v * cimag(typeof(v))))
        (r === nothing || iszero(r)) && return nothing
        E = gensym("E")
        rr = numerator(r) // denominator(r)
        xm, xp = :($xs ^ $(-rr)), :($xs ^ $rr)
        rep(t) = t isa Expr ? (t.head === :call && t.args[1] in (:sin, :cos) && length(t.args) == 2 && t.args[2] == arg ?
                 (t.args[1] === :sin ? :(($E * $xm - $xp / $E) / (2 * $I)) : :(($E * $xm + $xp / $E) / 2)) :
                 Expr(t.head, Any[rep(a) for a in t.args]...)) : t
        G = try
            risch_integrate(rep(f), xs; build = expr_build, lift = identity, verify = verify)
        catch e
            (e isa RischNotImplemented || e isa NotElementary) || rethrow()
            nothing
        end
        (G === nothing || G isa IntegralWithRootSums) && return nothing
        subst_symbols(G, Dict(E => :(exp($I * $arg) * $xp)))
    end
    isempty(sq) && return branch(1)
    Fp, Fm = branch(1), branch(-1)
    (Fp === nothing || Fm === nothing) && return nothing
    s, q = first(sq)
    σ = :($s / ($I * $q))
    :(((1 + $σ) * $Fp + (1 - $σ) * $Fm) / 2)
end

integrate_trig_log_imag(f, x; build = nothing, lift = nothing, verify::Bool = true) =
    integrate_rewritten_expr(f, x, (fe, xs) -> nothing, TZ_ACTIVE; build = build, lift = lift, verify = verify,
                             answer = (fe, xs) -> trig_log_imag_expr(fe, xs; verify = verify))

# step SE: a parameter p (a symbol) under a square root, √p, in f is s² with s a new symbol, √p = s: then the field
# knows s² = p, which as the opaque √p it did not (x⁶ atanh(√e x/√(d + e x²)): 1 - u² had a denominator that vanishes
# identically, sample 2843). An identity for every p (s = √p, principal); s is put back as √p. Expr in and out;
# nothing when f has no such root
function param_square_expr(f, xs::Symbol; verify::Bool = true)
    xk = string(xs)
    ps = Symbol[]
    function scan(t)
        t isa Expr || return
        if t.head === :call && ((t.args[1] === :sqrt && length(t.args) == 2) ||
                                (t.args[1] === :^ && length(t.args) == 3 && leaf_rational(t.args[3]) == 1//2))
            p = t.args[2]
            if p isa Symbol && string(p) != xk
                p in ps || push!(ps, p)
                return
            end
        end
        foreach(scan, t.args)
    end
    scan(f)
    isempty(ps) && return nothing
    ss = Dict(p => gensym(string(p)) for p in ps)
    function rw(t)
        t isa Symbol && haskey(ss, t) && return :($(ss[t]) ^ 2)
        t isa Expr || return t
        if t.head === :call && ((t.args[1] === :sqrt && length(t.args) == 2) ||
                                (t.args[1] === :^ && length(t.args) == 3 && leaf_rational(t.args[3]) == 1//2))
            t.args[2] isa Symbol && haskey(ss, t.args[2]) && return ss[t.args[2]]
        end
        Expr(t.head, Any[rw(a) for a in t.args]...)
    end
    G = try
        risch_integrate(rw(f), xs; build = expr_build, lift = identity, verify = verify)
    catch e
        (e isa RischNotImplemented || e isa NotElementary) || rethrow()
        nothing
    end
    (G === nothing || G isa IntegralWithRootSums) && return nothing
    subst_symbols(G, Dict(s => :(sqrt($p)) for (p, s) in ss))
end

integrate_param_square(f, x; build = nothing, lift = nothing, verify::Bool = true) =
    integrate_rewritten_expr(f, x, (fe, xs) -> nothing, SE_ACTIVE; build = build, lift = lift, verify = verify,
                             answer = (fe, xs) -> param_square_expr(fe, xs; verify = verify))
