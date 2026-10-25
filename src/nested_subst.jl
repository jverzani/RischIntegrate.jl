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
