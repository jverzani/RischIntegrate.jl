# ---------------------------------------------------------------------------
# Step LW: Lambert's W, W(x) eᵂ⁽ˣ⁾ = x (the name lambertw, as LambertW.jl and SymPy write it). With
# x = w eʷ, dx = (1 + w) eʷ dw, and W(x) = w:
#   ∫ R(x, W(x)) dx = ∫ R(w eʷ, w) (1 + w) eʷ dw,
# integrated in w, then w = W(x) put back with eᵏʷ = (x/W)ᵏ for an integer k. ∫ W(x) dx = eʷ(w² - w + 1)
# = (x/W)(W² - W + 1) = x (W - 1 + 1/W). For W(a x + b) (one argument, linear in x), x = (w eʷ - b)/a and
# eʷ = (a x + b)/W. Nothing when f has no W, or the integral in w is refused or not elementary (its
# RischNotImplemented or NotElementary).
# ---------------------------------------------------------------------------

# W(u) as a term: the operation lambertw, or a term printed so (SymEngine has no operation for it)
is_lambertw(t) = safe_iscall(t) && length(arguments(t)) == 1 &&
                 (opname(operation(t)) === :lambertw || startswith(string(t), "lambertw("))

function try_lambertw(f, x; build = nothing, lift = nothing, verify::Bool = true)
    @nospecialize f x
    xk = string(x)
    Wt = nothing                                        # the term W(a x + b) of f
    ok = true
    function find(t)
        safe_iscall(t) && !isempty(arguments(t)) || return
        if is_lambertw(t)
            Wt === nothing ? (Wt = t) : (string(arguments(t)[1]) == string(arguments(Wt)[1]) || (ok = false))
            return
        end
        foreach(find, arguments(t))
    end
    find(f)
    (ok && Wt !== nothing) || return nothing
    A = arguments(Wt)[1]
    T, el = try
        build_tower(A, xk)
    catch err
        (err isa RischNotImplemented || err isa RischError) || rethrow()
        return nothing
    end
    (isempty(T.levels) && degree(el.den) == 0 && degree(el.num) == 1) || return nothing
    a, b = el.num.c[2] / el.den.c[1], el.num.c[1] / el.den.c[1]
    bd = Builder(build === nothing ? auto_build(f, x) : build, lift === nothing ? auto_lift(f, x) : lift, x, T.consts)
    ew = mk(bd, :exp, bd.x)
    # x = (w eʷ - b)/a, with w written as x
    xw0 = iszero(b) ? mk(bd, :*, bd.x, ew) : mk(bd, :+, mk(bd, :*, bd.x, ew), cterm(bd, -b))
    xw = isone(a) ? xw0 : mk(bd, :/, xw0, cterm(bd, a))
    function walk(t)
        safe_iscall(t) || return string(t) == xk ? xw : t
        args = arguments(t)
        isempty(args) && return t
        is_lambertw(t) && return bd.x
        nargs = Any[walk(a) for a in args]
        all(i -> nargs[i] === args[i], eachindex(args)) ? t : term_rebuild(bd, t, nargs)
    end
    g = mk(bd, :*, walk(f), mk(bd, :+, bd.lift(1), bd.x), ew)
    isone(a) || (g = mk(bd, :/, g, cterm(bd, a)))
    G = risch_integrate(g, x; build = bd.build, lift = bd.lift, verify = verify)
    G isa IntegralWithRootSums && return nothing
    xW = mk(bd, :/, A, Wt)                              # eʷ = (a x + b)/W
    # k with u = k w, k an integer, else nothing
    function wmult(u)
        string(u) == xk && return 1
        k, hasw = Q(1), false
        for (t, e) in product_factors!(Any[], u, 1)
            if string(t) == xk && e == 1 && !hasw
                hasw = true
            else
                r = leaf_rational(t)
                r === nothing && return nothing
                k *= r^e
            end
        end
        (hasw && isone(denominator(k))) ? Int(numerator(k)) : nothing
    end
    function back(t)
        safe_iscall(t) || return string(t) == xk ? Wt : t
        args = arguments(t)
        isempty(args) && return t
        if opname(operation(t)) === :exp && length(args) == 1
            k = wmult(args[1])
            k === nothing || return k == 1 ? xW : mk(bd, :^, xW, bd.lift(k))
        end
        term_rebuild(bd, t, Any[back(a) for a in args])
    end
    back(G)
end
