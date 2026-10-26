# ---------------------------------------------------------------------------
# Step NS: a radical whose radicand has an inner radical √R(x) (nested radicals, Rubi 192, 467), after the usual
# route has failed. A substitution x = X(u) rationalizes the inner radical, √R = S(u):
#   R = (p x + q)/(r x + s):  u = √R,         x = (q - s u²)/(r u² - p),   S = u
#   R = x² + B x + C:         u = x + √R,     x = (u² - C)/(2u + B),       S = u - x   (Euler)
# (p, q, r, s, B, C free of x, possibly symbolic). The integrand f(X(u)) X′(u), with √R ↦ S(u), has the outer
# radical as a radical of a function of u; it is integrated as usual, and u = √R (resp. x + √R) put back.
# ---------------------------------------------------------------------------
const NESTED_SUBST = Ref(false)                         # no nested substitutions

# the radicands of radicals inside the radicands of other radicals of f
function inner_radicands(f, xk::String)
    out = Any[]
    function walk(t, inside::Bool)
        safe_iscall(t) || return
        args = arguments(t)
        isempty(args) && return
        rp = radical_parts(t)
        if rp !== nothing && depends_on(rp[2], xk)
            inside && !any(u -> string(u) == string(rp[2]), out) && push!(out, rp[2])
            walk(rp[2], true)
            return
        end
        foreach(a -> walk(a, inside), args)
    end
    walk(f, false)
    out
end

function try_nested_radical(f, x; build = nothing, lift = nothing, verify::Bool = true)
    @nospecialize f x
    NESTED_SUBST[] && return nothing
    xk = string(x)
    bd = Builder(build === nothing ? auto_build(f, x) : build, lift === nothing ? auto_lift(f, x) : lift, x)
    for R in inner_radicands(f, xk)
        sub = nested_substitution(bd, R, xk)
        sub === nothing && continue
        X, S, U = sub                                   # x = X(u), √R = S(u) (terms in x as u), u = U(x)
        Rs = string(R)
        function walk(t)
            safe_iscall(t) || return string(t) == xk ? X : t
            args = arguments(t)
            isempty(args) && return t
            rp = radical_parts(t)
            if rp !== nothing && string(rp[2]) == Rs    # R^e = S^(2e)
                k = 2 * rp[1]
                return isone(k) ? S : mk(bd, :^, S, isone(denominator(k)) ? bd.lift(Int(numerator(k))) : cterm(bd, k))
            end
            term_rebuild(bd, t, Any[walk(a) for a in args])
        end
        g = mk(bd, :*, walk(f), term_deriv(bd, X, xk))
        NESTED_SUBST[] = true
        G = try
            risch_integrate(g, x; build = build, lift = lift, verify = verify)
        catch e
            (e isa RischNotImplemented || e isa NotElementary) || rethrow()
            nothing
        finally
            NESTED_SUBST[] = false
        end
        G === nothing && continue
        back(t) = safe_iscall(t) && !isempty(arguments(t)) ? term_rebuild(bd, t, Any[back(a) for a in arguments(t)]) :
                  (string(t) == xk ? U : t)
        r = subst_answer(G, back, bd)                   # (a RootSum in u: its variable stands for U)
        r === nothing || return r
    end
    nothing
end

# (X(u), S(u), U(x)) for the inner radicand R (see the header), else nothing
function nested_substitution(bd::Builder, R, xk::String)
    neg(t) = mk(bd, :*, bd.lift(-1), t)
    sq(t) = mk(bd, :^, t, bd.lift(2))
    u = bd.x
    # (p x + q)/(r x + s), or p x + q
    num, den = R, nothing
    if safe_iscall(R) && opname(operation(R)) === :/ && length(arguments(R)) == 2
        num, den = arguments(R)
    end
    N = poly_parts(bd, num, xk)
    D = den === nothing ? Dict{Int,Any}(0 => bd.lift(1)) : poly_parts(bd, den, xk)
    if N !== nothing && D !== nothing && maximum(keys(N)) <= 1 && maximum(keys(D)) <= 1 &&
       (maximum(keys(N)) == 1 || maximum(keys(D)) == 1)
        z = bd.lift(0)
        p, q, r, s = get(N, 1, z), get(N, 0, z), get(D, 1, z), get(D, 0, z)
        X = mk(bd, :/, mk(bd, :+, q, neg(mk(bd, :*, s, sq(u)))), mk(bd, :+, mk(bd, :*, r, sq(u)), neg(p)))
        return (X, u, mk(bd, :sqrt, R))
    end
    # 1 + 1/x and the like: R as a sum with a term c/x (one fraction): (c + q x)/x
    if N === nothing && safe_iscall(R) && opname(operation(R)) === :+
        cs, qs = Any[], Any[]
        for t in arguments(R)
            if safe_iscall(t) && opname(operation(t)) === :/ && length(arguments(t)) == 2 &&
               string(arguments(t)[2]) == xk && !depends_on(arguments(t)[1], xk)
                push!(cs, arguments(t)[1])
            elseif !depends_on(t, xk)
                push!(qs, t)
            else
                return nothing
            end
        end
        (isempty(cs) || isempty(qs)) && return nothing
        c = length(cs) == 1 ? cs[1] : mk(bd, :+, cs...)
        q = length(qs) == 1 ? qs[1] : mk(bd, :+, qs...)
        X = mk(bd, :/, c, mk(bd, :+, sq(u), neg(q)))      # R = q + c/x = u²: x = c/(u² - q)
        return (X, u, mk(bd, :sqrt, R))
    end
    # x² + B x + C (Euler)
    if N !== nothing && den === nothing && maximum(keys(N)) == 2
        A2 = leaf_rational(N[2])
        (A2 !== nothing && isone(A2)) || return nothing
        z = bd.lift(0)
        Bc, Cc = get(N, 1, z), get(N, 0, z)
        X = mk(bd, :/, mk(bd, :+, sq(u), neg(Cc)), mk(bd, :+, mk(bd, :*, bd.lift(2), u), Bc))
        return (X, mk(bd, :+, u, neg(X)), mk(bd, :+, bd.x, mk(bd, :sqrt, R)))
    end
    nothing
end

# ---------------------------------------------------------------------------
# Step PP: two square roots √(g + c₁), √(g + c₂) of one term g, k = c₁ - c₂ > 0 (Rubi 262: √(√(sec x + 1) - √(sec x - 1))).
# For g = x, w = √(x + c₁) - √(x + c₂) rationalizes both (their sum is k/w):
#   √(x + c₁) = (w + k/w)/2,  √(x + c₂) = (k/w - w)/2,  x = ((w + k/w)/2)² - c₁,
# so a radicand √(x + c₁) - √(x + c₂) becomes w. For g = h(a x + b), h = sec, csc, sin, cos, tan, cot, exp, sinh, cosh,
# first u = g (every x of f inside g), dx = du/(a h′(u)) with h′ written in u (sec: u √(u + 1) √(u - 1), u > 1, tan > 0;
# the answer holds there), integrated as usual (then the case g = x), and u = g put back.
# ---------------------------------------------------------------------------
const PAIR_SUBST = Ref(0)                               # nesting depth (u = g, then w)

# (g, c) when R = g + c with g a term in x and c rational, else nothing
function shift_parts(R, xk::String)
    safe_iscall(R) || return string(R) == xk ? (R, Q(0)) : nothing
    n, args = opname(operation(R)), arguments(R)
    terms = n === :+ ? Any[(a, 1) for a in args] :
            (n === :- && length(args) == 2) ? Any[(args[1], 1), (args[2], -1)] : Any[(R, 1)]
    g, c = nothing, Q(0)
    for (t, s) in terms
        r = leaf_rational(t)
        if r !== nothing
            c += s * Q(r)
        elseif depends_on(t, xk) && g === nothing && s == 1
            g = t
        else
            return nothing
        end
    end
    g === nothing ? nothing : (g, c)
end

function try_pair_radical(f, x; build = nothing, lift = nothing, verify::Bool = true)
    @nospecialize f x
    PAIR_SUBST[] < 2 || return nothing
    xk = string(x)
    bd = Builder(build === nothing ? auto_build(f, x) : build, lift === nothing ? auto_lift(f, x) : lift, x)
    shifts = Dict{String,Vector{Any}}()                 # g ↦ [(c, g)]
    for (e, R) in collect_radicals(f, xk)
        denominator(2 * e) == 1 || continue
        sp = shift_parts(R, xk)
        sp === nothing && continue
        g, c = sp
        v = get!(shifts, string(g), Any[])
        any(p -> p[1] == c, v) || push!(v, (c, g))
    end
    for (gk, v) in shifts
        length(v) == 2 || continue
        (c1, g), (c2, _) = v[1][1] > v[2][1] ? (v[1], v[2]) : (v[2], v[1])
        sub = gk == xk ? pair_subst(f, bd, xk, c1, c2) : pair_function_subst(f, bd, xk, g)
        sub === nothing && continue
        integrand, back = sub
        PAIR_SUBST[] += 1
        G = try
            risch_integrate(integrand, x; build = build, lift = lift, verify = verify)
        catch e
            (e isa RischNotImplemented || e isa NotElementary) || rethrow()
            nothing
        finally
            PAIR_SUBST[] -= 1
        end
        G === nothing && continue
        bk(t) = isnode(t) ? term_rebuild(bd, t, Any[bk(a) for a in arguments(t)]) : (string(t) == xk ? back : t)
        r = subst_answer(G, bk, bd)
        r === nothing || return r
    end
    nothing
end

# g = x: f(X(w)) X′(w) with the two radicals replaced, and the back-substitution w = √(x + c₁) - √(x + c₂)
function pair_subst(f, bd::Builder, xk::String, c1::Q, c2::Q)
    k = c1 - c2
    w = bd.x
    kw = mk(bd, :/, cterm(bd, k), w)
    S1 = mk(bd, :/, mk(bd, :+, w, kw), bd.lift(2))
    S2 = mk(bd, :/, mk(bd, :+, kw, mk(bd, :*, bd.lift(-1), w)), bd.lift(2))
    X = mk(bd, :+, mk(bd, :^, S1, bd.lift(2)), cterm(bd, -c1))
    # ±1 when t = √(x + c₁) - √(x + c₂) (resp. its negative), else 0
    function isdiff(t)
        safe_iscall(t) || return 0
        n, args = opname(operation(t)), arguments(t)
        terms = n === :+ ? Any[(a, 1) for a in args] : (n === :- && length(args) == 2) ? Any[(args[1], 1), (args[2], -1)] : Any[]
        length(terms) == 2 || return 0
        sg = Dict{Q,Int}()
        for (a, s) in terms
            fs = product_factors!(Any[], a, 1)
            r = nothing
            for (fa, e) in fs
                if leaf_rational(fa) !== nothing && e == 1 && leaf_rational(fa) == -1
                    s = -s
                elseif (rp = radical_parts(fa)) !== nothing && rp[1] == Q(1, 2) && e == 1 && r === nothing
                    r = rp[2]
                else
                    return 0
                end
            end
            r === nothing && return 0
            sp = shift_parts(r, xk)
            (sp === nothing || string(sp[1]) != xk) && return 0
            sg[sp[2]] = s
        end
        (get(sg, c1, 0) == 1 && get(sg, c2, 0) == -1) ? 1 : (get(sg, c1, 0) == -1 && get(sg, c2, 0) == 1) ? -1 : 0
    end
    function walk(t)
        safe_iscall(t) || return string(t) == xk ? X : t
        args = arguments(t)
        isempty(args) && return t
        rp = radical_parts(t)
        if rp !== nothing && isdiff(rp[2]) == 1                 # (√(x + c₁) - √(x + c₂))^e = w^e
            return mk(bd, :^, w, cterm(bd, rp[1]))
        end
        if rp !== nothing
            sp = shift_parts(rp[2], xk)
            if sp !== nothing && string(sp[1]) == xk && (sp[2] == c1 || sp[2] == c2) && denominator(2 * rp[1]) == 1
                S = sp[2] == c1 ? S1 : S2
                p = Int(numerator(2 * rp[1]))
                return p == 1 ? S : mk(bd, :^, S, bd.lift(p))
            end
        end
        term_rebuild(bd, t, Any[walk(a) for a in args])
    end
    g = mk(bd, :*, walk(f), term_deriv(bd, X, xk))
    xt(c) = mk(bd, :+, bd.x, cterm(bd, c))
    back = mk(bd, :+, mk(bd, :sqrt, xt(c1)), mk(bd, :*, bd.lift(-1), mk(bd, :sqrt, xt(c2))))
    (g, back)
end

# g = h(a x + b): f in u = g times dx/du, and the back-substitution u = g; nothing when x appears outside g
function pair_function_subst(f, bd::Builder, xk::String, g)
    isnode(g) && length(arguments(g)) == 1 || return nothing
    h = opname(operation(g))
    pp = poly_parts(bd, arguments(g)[1], xk)
    (pp === nothing || !haskey(pp, 1) || maximum(keys(pp)) != 1) && return nothing
    a = pp[1]
    u = bd.x
    one_ = bd.lift(1)
    neg(t) = mk(bd, :*, bd.lift(-1), t)
    sq(t) = mk(bd, :sqrt, t)
    up(c) = mk(bd, :+, u, bd.lift(c))                   # u + c
    um(c) = mk(bd, :+, bd.lift(c), neg(u))              # c - u
    u2(c) = mk(bd, :+, mk(bd, :^, u, bd.lift(2)), bd.lift(c))
    # h′ in terms of u
    hp = h === :sec ? mk(bd, :*, u, sq(up(1)), sq(up(-1))) :
         h === :csc ? neg(mk(bd, :*, u, sq(up(1)), sq(up(-1)))) :
         h === :sin ? mk(bd, :*, sq(um(1)), sq(up(1))) :
         h === :cos ? neg(mk(bd, :*, sq(um(1)), sq(up(1)))) :
         h === :tan ? u2(1) : h === :cot ? neg(u2(1)) :
         h === :exp ? u :
         h === :sinh ? sq(u2(1)) : h === :cosh ? mk(bd, :*, sq(up(1)), sq(up(-1))) : nothing
    hp === nothing && return nothing
    gs = string(g)
    ok = Ref(true)
    function walk(t)
        string(t) == gs && return u
        if !safe_iscall(t) || isempty(arguments(t))
            string(t) == xk && (ok[] = false)
            return t
        end
        term_rebuild(bd, t, Any[walk(s) for s in arguments(t)])
    end
    fu = walk(f)
    ok[] || return nothing
    (mk(bd, :/, fu, mk(bd, :*, a, hp)), g)
end
