# ---------------------------------------------------------------------------
# Step AS: asin and acos by the substitution u = sin t (u = cos t)
#
# All asin(u) (or all acos(u)) in f must share one linear u = a x + b (asin and acos together would
# need π). The integrand is rebuilt in the user's package with x playing the role of t:
#   asin:  x ↦ (sin x - b)/a,  asin(u) ↦ x,  √(1 - u²) ↦ cos x,  dx ↦ cos x/a dx
#   acos:  x ↦ (cos x - b)/a,  acos(u) ↦ x,  √(1 - u²) ↦ sin x,  dx ↦ -sin x/a dx
# (principal branches: t ∈ (-π/2, π/2) resp. (0, π), where cos t resp. sin t is ≥ 0), integrated by
# `risch_integrate` (verified there), and the answer mapped back: x ↦ asin(u), and sin(kx), cos(kx),
# tan(kx) (k ∈ ℤ), tan(x/2) through (cos t + i sin t)^k computed exactly as A(u) + B(u)·√(1 - u²)
# (with √(1 - u²)² = 1 - u²). By the chain rule the result is an antiderivative for -1 < u < 1.
# ---------------------------------------------------------------------------

# when every radical of f is q^(k/2) for one quadratic q = K (1 - u²), u = a x + b linear (a > 0), with
# √K rational (completing the square: K = γ - β²/(4α), α < 0): (arcs list [(:asin, u term,
# asin(u) term)], √K) for an asin substitution, else nothing
function unit_circle_radicand(f, x, rads, xk::String; build = nothing, lift = nothing)
    @nospecialize f x
    all(r -> denominator(r[1]) == 2, rads) || return nothing
    q = radicand_element(rads[1][2], xk)
    (q !== nothing && isone(q.den) && degree(q.num) == 2) || return nothing
    all(r -> radicand_element(r[2], xk) == q, rads) || return nothing
    γ, β, α = q.num.c
    α < 0 || return nothing
    K = γ - β^2 / (4α)
    K > 0 || return nothing
    sK, a = rat_sqrt(K), rat_sqrt(-α / K)
    (sK === nothing || a === nothing) && return nothing
    b = a * β / (2α)                                    # u = a (x + β/(2α))
    bd = Builder(build === nothing ? auto_build(f, x) : build, lift === nothing ? auto_lift(f, x) : lift, x)
    ut = poly_term(bd, UPoly{Q}(Q[b, a]))
    Any[(:asin, ut, mk(bd, :asin, ut))], sK, rads[1][2]
end

# step IH: the inverse hyperbolic functions as logarithms (Julia's definitions, real where the function is):
#   atanh u = ½ log((1 + u)/(1 - u)),  acoth u = ½ log((u + 1)/(u - 1)),
#   asinh u = log(u + √(u² + 1)),      acosh u = log(u + √(u² - 1))  (u ≥ 1),
#   acsch u = asinh(1/u),              asech u = acosh(1/u) = log((1 + √(1 - u²))/u)  (0 < u ≤ 1)
const INV_HYP = (:atanh, :acoth, :asinh, :acosh, :acsch, :asech)
function rewrite_invhyp(f, x, build, lift)
    @nospecialize f x
    bd = Builder(build === nothing ? auto_build(f, x) : build, lift === nothing ? auto_lift(f, x) : lift, x)
    half(t) = mk(bd, :*, bd.lift(1 // 2), t)
    neg(t) = mk(bd, :*, bd.lift(-1), t)
    sq(u) = mk(bd, :^, u, bd.lift(2))
    function rw(t)
        safe_iscall(t) && !isempty(arguments(t)) || return t
        args = Any[rw(a) for a in arguments(t)]
        n = opname(operation(t))
        if n in INV_HYP && length(args) == 1
            n === :asech && return mk(bd, :log, mk(bd, :/, mk(bd, :+, bd.lift(1), mk(bd, :sqrt, mk(bd, :+, bd.lift(1), neg(sq(args[1]))))),
                                                   args[1]))
            u = n === :acsch ? mk(bd, :/, bd.lift(1), args[1]) : args[1]
            n === :atanh && return half(mk(bd, :log, mk(bd, :/, mk(bd, :+, bd.lift(1), u), mk(bd, :+, bd.lift(1), neg(u)))))
            n === :acoth && return half(mk(bd, :log, mk(bd, :/, mk(bd, :+, u, bd.lift(1)), mk(bd, :+, u, bd.lift(-1)))))
            n in (:asinh, :acsch) && return mk(bd, :log, mk(bd, :+, u, mk(bd, :sqrt, mk(bd, :+, sq(u), bd.lift(1)))))
            return mk(bd, :log, mk(bd, :+, u, mk(bd, :sqrt, mk(bd, :+, sq(u), bd.lift(-1)))))
        end
        term_rebuild(bd, t, args)
    end
    rw(f)
end

has_op(f, n::Symbol) = safe_iscall(f) && !isempty(arguments(f)) &&
                       (opname(operation(f)) === n || any(a -> has_op(a, n), arguments(f)))
# step AC: acot(u) ↦ atan(1/u) (Julia's definition, all u ≠ 0)
function rewrite_acot(f, x, build, lift)
    @nospecialize f x
    bd = Builder(build === nothing ? auto_build(f, x) : build, lift === nothing ? auto_lift(f, x) : lift, x)
    function rw(t)
        safe_iscall(t) && !isempty(arguments(t)) || return t
        args = Any[rw(a) for a in arguments(t)]
        opname(operation(t)) === :acot && length(args) == 1 &&
            return mk(bd, :atan, mk(bd, :/, bd.lift(1), args[1]))
        term_rebuild(bd, t, args)
    end
    rw(f)
end

# [(kind, argument term, whole term)] of the asin / acos / acsc / asec subterms of f (`fns`: other functions)
function collect_arcs(f, xk::String, out = Any[]; fns = (:asin, :acos, :acsc, :asec))
    if safe_iscall(f)
        args = arguments(f)
        n = opname(operation(f))
        n in fns && length(args) == 1 && push!(out, (n, args[1], f))
        for a in args
            collect_arcs(a, xk, out; fns = fns)
        end
    end
    out
end

# rebuild a term with its arguments mapped (operations called as functions, as in `term_value`)
function term_rebuild(b::Builder, t, args)
    b.build(op_function(t), args...)
end

# step AL: asin, acos, acsc, asec of a x + b with a, b free of x but not rational (asin(a x), the parameter a): y = a x + b,
# ∫ f dx = ∫ f((y - b)/a) dy/a with the arcs of y, then y = a x + b. Nothing when the arguments differ or are not linear.
# The same for the inverse hyperbolic functions (step IH), so (a + b asinh(c x))/√(1 + c²x²) is integrated as
# (a + b asinh y)/√(1 + y²) (after step RC has taken d out of √(d + c²d x²)).
const ARC_SCALED = (:asin, :acos, :acsc, :asec, :asinh, :acosh, :atanh, :acoth, :acsch, :asech)
function integrate_arcs_scaled(f, x, arcs; build = nothing, lift = nothing, verify::Bool = true)
    @nospecialize f x
    xk = string(x)
    L = arcs[1][2]
    Ls = string(L)
    all(a -> string(a[2]) == Ls, arcs) || return nothing
    u = radicand_element(L, xk)
    (u !== nothing && isone(u.den) && degree(u.num) == 1) && return nothing        # (rational: integrate_arcsin)
    bd = Builder(build === nothing ? auto_build(f, x) : build, lift === nothing ? auto_lift(f, x) : lift, x)
    pp = poly_parts(bd, L, xk)
    (pp === nothing || !haskey(pp, 1) || maximum(keys(pp)) != 1) && return nothing
    a = pp[1]
    b = get(pp, 0, nothing)
    y = bd.x
    X = b === nothing ? mk(bd, :/, y, a) : mk(bd, :/, mk(bd, :+, y, mk(bd, :*, bd.lift(-1), b)), a)
    function walk(t)
        isnode(t) || return string(t) == xk ? X : t
        n = opname(operation(t))
        (n in ARC_SCALED && length(arguments(t)) == 1 && string(arguments(t)[1]) == Ls) &&
            return term_rebuild(bd, t, Any[y])
        rp = radical_parts(t)
        if rp !== nothing && depends_on(rp[2], xk)      # a radicand as a polynomial in y (1 - c²x² ↦ 1 - y²)
            R = walk(rp[2])
            pr = poly_parts(bd, R, xk)
            if pr !== nothing
                # each coefficient through the constant field (a²·a⁻²·(-1) ↦ -1)
                function csimp(c)
                    T, el = try
                        build_tower(c, xk)
                    catch err
                        (err isa RischNotImplemented || err isa RischError) || rethrow()
                        return c
                    end
                    (isempty(T.levels) && degree(el.num) <= 0 && degree(el.den) == 0) || return c
                    v = isempty(el.num.c) ? zero(ctype(T)) : el.num.c[1] / el.den.c[1]
                    cterm(Builder(bd.build, bd.lift, bd.x, T.consts), v)
                end
                ts = Any[]
                for (k, c) in sort(collect(pr); by = first)
                    c = csimp(c)
                    iszero(leaf_rational(c) === nothing ? 1 : leaf_rational(c)) && continue
                    push!(ts, k == 0 ? c : mk(bd, :*, c, k == 1 ? y : mk(bd, :^, y, bd.lift(k))))
                end
                R = length(ts) == 1 ? ts[1] : mk(bd, :+, ts...)
            end
            return mk(bd, :^, R, cterm(bd, rp[1]))
        end
        term_rebuild(bd, t, Any[walk(s) for s in arguments(t)])
    end
    # f(X)/a as one product, the powers xᵏ of a pure scaling written yᵏ a⁻ᵏ: the factors free of x come out (step IT)
    cs, gs = Any[mk(bd, :^, a, bd.lift(-1))], Any[]
    for (t, e) in product_factors!(Any[], f, 1)
        if b === nothing && !isnode(t) && string(t) == xk
            push!(gs, mk(bd, :^, y, bd.lift(e)))
            push!(cs, mk(bd, :^, a, bd.lift(-e)))
        else
            w = walk(t)
            push!(gs, e == 1 ? w : mk(bd, :^, w, bd.lift(e)))
        end
    end
    g = mk(bd, :*, cs..., gs...)
    # the radicands rewritten in y keep a parameter factor (d + d y² from d + c²d x²): out (step RK), so that the
    # radical is u′'s, √(1 + y²) for asinh y
    g2 = split_radicand_content(g, x, xk, build, lift)
    (g2 !== nothing && any(a -> a[1] in INV_HYP, arcs)) && (g = g2)
    G = risch_integrate(g, x; build = build, lift = lift, verify = verify)
    back(t) = isnode(t) ? term_rebuild(bd, t, Any[back(s) for s in arguments(t)]) : (string(t) == xk ? L : t)
    subst_answer(G, back, bd)
end

function integrate_arcsin(f, x, arcs; sK::Q = Q(1), radicand = nothing, build = nothing, lift = nothing,
                          verify::Bool = true)
    @nospecialize f x
    xk = string(x)
    kind = arcs[1][1]
    all(a -> a[1] === kind, arcs) || throw(RischNotImplemented(
        "different inverse trigonometric functions together (relations between them need π)"))
    # step AC: acsc(u) = asin(1/u), asec(u) = acos(1/u): 1/u = sin t (cos t), u = 1/sin t; with the
    # radical √(u² - 1) = r/p this is valid for u > 1 (principal branch, t ∈ (0, π/2))
    recip = kind in (:acsc, :asec)
    u = radicand_element(arcs[1][2], xk)
    (u !== nothing && isone(u.den) && degree(u.num) == 1) || throw(RischNotImplemented(
        "asin/acos of $(arcs[1][2]): only linear arguments a x + b are supported"))
    all(a -> radicand_element(a[2], xk) == u, arcs) || throw(RischNotImplemented(
        "asin/acos of different arguments"))
    a, b = u.num.c[2], u.num.c[1]
    bd = Builder(build === nothing ? auto_build(f, x) : build, lift === nothing ? auto_lift(f, x) : lift, x)
    issin = kind in (:asin, :acsc)
    st, ct = mk(bd, :sin, bd.x), mk(bd, :cos, bd.x)
    pt, rt = issin ? (st, ct) : (ct, st)                 # u = p(t) (recip: 1/u = p(t)), √(1 - p²) = r(t)
    xt = mk(bd, :/, mk(bd, :+, recip ? mk(bd, :/, bd.lift(1), pt) : pt, cterm(bd, -b)), cterm(bd, a))
    one_minus_u2 = frac(UPoly{Q}(Q[1])) - u * u
    rad = frac(UPoly{Q}(Q[sK^2])) * (recip ? -one_minus_u2 : one_minus_u2)   # K(1 - u²), recip: K(u² - 1)
    function sub(t)
        if safe_iscall(t) && !isempty(arguments(t))
            n = opname(operation(t))
            n in (:asin, :acos, :acsc, :asec) && return bd.x
            rp = radical_parts(t)
            if rp !== nothing && denominator(rp[1]) == 2 && radicand_element(rp[2], xk) == rad
                e = Int(numerator(rp[1]))               # (K (1 - u²))^(e/2) = (√K)^e r^e
                base = recip ? mk(bd, :/, rt, pt) : rt  # recip: √(u² - 1) = r/p (u > 0)
                re = e == 1 ? base : mk(bd, :^, base, bd.lift(e))
                return isone(sK) ? re : mk(bd, :*, cterm(bd, sK^e), re)
            end
            return term_rebuild(bd, t, Any[sub(s) for s in arguments(t)])
        end
        string(t) == xk ? xt : t
    end
    dxdt = recip ? mk(bd, :/, mk(bd, :*, cterm(bd, (issin ? -1 : 1) // a), rt), mk(bd, :^, pt, bd.lift(2))) :
                   mk(bd, :*, cterm(bd, (issin ? 1 : -1) // a), rt)
    g = mk(bd, :*, sub(f), dxdt)
    G = risch_integrate(g, x; build = build, lift = lift, verify = verify)
    G isa IntegralWithRootSums && throw(RischNotImplemented("a RootSum after an arcsine substitution"))
    # map back
    arcterm = arcs[1][3]
    bu = Builder(bd.build, bd.lift, arcs[1][2])        # polynomials in u printed with the u term
    P = UPoly{Q}
    sP = xpoly(Q)
    rr = P(Q[1, 0, -1])                                 # 1 - u²
    # √(1 - u²) in the answer: the integrand's own radical √q / √K when there is one;
    # recip (s = 1/u): √(1 - 1/u²) itself (√(u² - 1)/u would hold for u > 1 only)
    rterm = recip ? mk(bd, :sqrt, frac_term(bu, frac(P(Q[-1, 0, 1]), P(Q[0, 0, 1])))) :
            radicand === nothing ? mk(bd, :sqrt, poly_term(bu, rr)) :
            isone(sK) ? mk(bd, :sqrt, radicand) : mk(bd, :/, mk(bd, :sqrt, radicand), cterm(bd, sK))
    # a polynomial in s as a term: recip: s = 1/u, A(1/u) = (reversed A)(u)/u^deg A
    sterm(A) = recip ? frac_term(bu, frac(P(reverse(vcat(A.c, fill(Q(0), 0)))), xpoly(Q)^degree(A))) :
                       poly_term(bu, A)
    mul((A1, B1), (A2, B2)) = (A1 * A2 + rr * B1 * B2, A1 * B2 + A2 * B1)
    sub2((A1, B1), (A2, B2)) = (A1 - A2, B1 - B2)
    add2((A1, B1), (A2, B2)) = (A1 + A2, B1 + B2)
    zP = (zero(P), zero(P))
    ccos, csin = issin ? ((zero(P), one(P)), (sP, zero(P))) : ((sP, zero(P)), (zero(P), one(P)))
    function cis(k::Int)                                # (cos kt, sin kt) as pairs
        c, sn = (one(P), zero(P)), zP
        for _ in 1:abs(k)
            c, sn = sub2(mul(c, ccos), mul(sn, csin)), add2(mul(c, csin), mul(sn, ccos))
        end
        k < 0 ? (c, (-sn[1], -sn[2])) : (c, sn)
    end
    function pterm((A, B))
        ts = Any[]
        iszero(A) || push!(ts, sterm(A))
        if !iszero(B)
            push!(ts, isone(B) ? rterm : mk(bd, :*, sterm(B), rterm))
        end
        isempty(ts) ? bd.lift(0) : length(ts) == 1 ? ts[1] : mk(bd, :+, ts...)
    end
    function back(t)
        if safe_iscall(t) && !isempty(arguments(t))
            n = opname(operation(t))
            args = arguments(t)
            if n in (:sin, :cos, :tan, :cot) && length(args) == 1
                e = radicand_element(args[1], xk)
                if e !== nothing && isone(e.den) && degree(e.num) == 1 && iszero(e.num.c[1])
                    c = e.num.c[2]
                    if isone(denominator(c))
                        cc, sn = cis(Int(numerator(c)))
                        n === :sin && return pterm(sn)
                        n === :cos && return pterm(cc)
                        n === :cot && return mk(bd, :/, pterm(cc), pterm(sn))
                        return mk(bd, :/, pterm(sn), pterm(cc))
                    elseif c == 1 // 2 && n === :tan          # tan(t/2) = sin t/(1 + cos t)
                        return mk(bd, :/, pterm(csin), mk(bd, :+, bd.lift(1), pterm(ccos)))
                    elseif c == 1 // 2 && n === :cot          # cot(t/2) = (1 + cos t)/sin t
                        return mk(bd, :/, mk(bd, :+, bd.lift(1), pterm(ccos)), pterm(csin))
                    end
                end
            end
            return term_rebuild(bd, t, Any[back(s) for s in args])
        end
        string(t) == xk ? arcterm : t
    end
    tidy_terms(bd, back(G), xk)
end

# Tidy a term (step AC): in products/quotients/powers, the factors that are rational functions of x
# are multiplied out into one canonical rational factor; in sums, terms with the same non-rational
# part (compared as printed) are collected by adding their rational coefficients. Exact: the
# rational parts are elements of ℚ(x) (`radicand_element`), the rest is kept as it is.
function tidy_terms(bd::Builder, t, xk::String)
    isrational(a) = (r = radicand_element(a, xk); r)
    # (rational coefficient ∈ ℚ(x), [(non-rational factor, integer exponent)])
    function split(a)
        r = isrational(a)
        r === nothing || return (r, Any[])
        if safe_iscall(a) && !isempty(arguments(a))
            n, args = opname(operation(a)), arguments(a)
            if n === :* || (n === :- && length(args) == 1)
                R, F = frac(UPoly{Q}(Q[n === :- ? -1 : 1])), Any[]
                for b in args
                    rb, fb = split(b)
                    R = R * rb
                    append!(F, fb)
                end
                return (R, F)
            elseif n === :/ && length(args) == 2
                r1, f1 = split(args[1])
                r2, f2 = split(args[2])
                iszero(r2) && return (frac(UPoly{Q}(Q[1])), Any[(a, 1)])
                return (r1 / r2, vcat(f1, [(g, -e) for (g, e) in f2]))
            elseif n === :^ && length(args) == 2
                e = leaf_rational(args[2])
                if e !== nothing && isone(denominator(e))
                    rb, fb = split(args[1])
                    k = Int(numerator(e))
                    (k < 0 && iszero(rb)) && return (frac(UPoly{Q}(Q[1])), Any[(a, 1)])
                    return (rb^k, [(g, ex * k) for (g, ex) in fb])
                end
            end
        end
        (frac(UPoly{Q}(Q[1])), Any[(a, 1)])
    end
    function build((R, F))
        iszero(R) && return bd.lift(0)
        num = Any[]
        den = Any[]
        for (g, e) in F
            e == 0 && continue
            tg = abs(e) == 1 ? g : mk(bd, :^, g, bd.lift(abs(e)))
            push!(e > 0 ? num : den, tg)
        end
        isone(R) || pushfirst!(num, frac_term(bd, R))
        nt = isempty(num) ? bd.lift(1) : length(num) == 1 ? num[1] : mk(bd, :*, num...)
        isempty(den) ? nt : mk(bd, :/, nt, length(den) == 1 ? den[1] : mk(bd, :*, den...))
    end
    function tidy(a)
        (safe_iscall(a) && !isempty(arguments(a))) || return a
        n = opname(operation(a))
        args = Any[tidy(b) for b in arguments(a)]
        a = term_rebuild(bd, a, args)
        if n === :+ || n === :-
            terms = n === :+ ? args : (length(args) == 1 ? Any[mk(bd, :*, bd.lift(-1), args[1])] :
                                       Any[args[1], mk(bd, :*, bd.lift(-1), args[2])])
            groups = Dict{String,Any}()
            order = String[]
            for b in terms
                R, F = split(b)
                key = join(sort([string(g) * "^" * string(e) for (g, e) in F]), "*")
                if haskey(groups, key)
                    groups[key] = (groups[key][1] + R, groups[key][2])
                else
                    groups[key] = (R, F)
                    push!(order, key)
                end
            end
            parts = Any[build(groups[k]) for k in order if !iszero(groups[k][1])]
            isempty(parts) && return bd.lift(0)
            return length(parts) == 1 ? parts[1] : mk(bd, :+, parts...)
        elseif n in (:*, :/, :^)
            R, F = split(a)
            # R · (s₁ + s₂ + …): distribute the rational factor over a single sum, then collect
            if length(F) == 1 && F[1][2] == 1 && safe_iscall(F[1][1]) && opname(operation(F[1][1])) === :+ &&
               !isone(R)
                Rt = frac_term(bd, R)
                return tidy(mk(bd, :+, Any[mk(bd, :*, Rt, b) for b in arguments(F[1][1])]...))
            end
            return build((R, F))
        end
        a
    end
    tidy(t)
end

# ---------------------------------------------------------------------------
# Step AT: atan by the substitution u = tan t, after the usual route has failed (∫ x atan(x)/(1 + x²),
# ∫ atan(x)/x: Clausen forms by step CL). All atan(u) in f share one linear u = a x + b; with x playing
# the role of t:
#   x ↦ (tan x - b)/a,  atan(u) ↦ x,  √(1 + u²) ↦ 1/cos x,  dx ↦ 1/(a cos² x) dx,
# valid for all real u (t ∈ (-π/2, π/2), cos t > 0). The answer is mapped back with x ↦ atan(u) and
# cos kt + i sin kt = (1 + i u)^k / (1 + u²)^(k/2) for k ∈ ℤ, tan(t/2) = u/(1 + √(1 + u²)).
# ---------------------------------------------------------------------------
const ATAN_SUBST = Ref(false)                           # no nested substitutions

function collect_atans(f, out = Any[])
    if safe_iscall(f)
        args = arguments(f)
        opname(operation(f)) === :atan && length(args) == 1 && push!(out, f)
        foreach(a -> collect_atans(a, out), args)
    end
    out
end

function try_atan_subst(f, x; build = nothing, lift = nothing, verify::Bool = true)
    @nospecialize f x
    ATAN_SUBST[] && return nothing
    xk = string(x)
    ats = collect_atans(f)
    isempty(ats) && return nothing
    any(n -> has_op(f, n), (:acot, :asin, :acos, :asec, :acsc)) && return nothing   # (relations need π)
    u = radicand_element(arguments(ats[1])[1], xk)
    (u !== nothing && isone(u.den) && degree(u.num) == 1) || return nothing
    all(t -> radicand_element(arguments(t)[1], xk) == u, ats) || return nothing
    a, b = u.num.c[2], u.num.c[1]
    one_plus_u2 = frac(UPoly{Q}(Q[1])) + u * u
    bd = Builder(build === nothing ? auto_build(f, x) : build, lift === nothing ? auto_lift(f, x) : lift, x)
    ct = mk(bd, :cos, bd.x)
    xt = mk(bd, :/, mk(bd, :+, mk(bd, :tan, bd.x), cterm(bd, -b)), cterm(bd, a))
    function sub(t)
        if safe_iscall(t) && !isempty(arguments(t))
            opname(operation(t)) === :atan && return bd.x
            rp = radical_parts(t)
            if rp !== nothing && denominator(rp[1]) == 2
                q = radicand_element(rp[2], xk)
                if q !== nothing && isone(q.den) && degree(q.num) == 2
                    K = q.num.c[1]                      # q = K (1 + u²) with √K rational
                    sK = K > 0 ? rat_sqrt(K) : nothing
                    if sK !== nothing && q == frac(UPoly{Q}(Q[K])) * one_plus_u2
                        e = Int(numerator(rp[1]))       # (K (1 + u²))^(e/2) = (√K)^e / cos^e t
                        re = mk(bd, :/, cterm(bd, sK^e), e == 1 ? ct : mk(bd, :^, ct, bd.lift(e)))
                        return re
                    end
                end
            end
            return term_rebuild(bd, t, Any[sub(s) for s in arguments(t)])
        end
        string(t) == xk ? xt : t
    end
    g = mk(bd, :/, sub(f), mk(bd, :*, cterm(bd, a), mk(bd, :^, ct, bd.lift(2))))
    ATAN_SUBST[] = true
    G = try
        risch_integrate(g, x; build = build, lift = lift, verify = verify)
    catch e
        (e isa RischNotImplemented || e isa NotElementary) || rethrow()
        nothing
    finally
        ATAN_SUBST[] = false
    end
    (G === nothing || G isa IntegralWithRootSums) && return nothing
    # map back
    arcterm = ats[1]
    bu = Builder(bd.build, bd.lift, arguments(ats[1])[1])     # rational functions of u printed with the u term
    P = UPoly{Q}
    w = P(Q[1, 0, 1])                                   # 1 + u²
    rterm = mk(bd, :sqrt, poly_term(bu, w))             # √(1 + u²)
    function cis(k::Int)                                # (1 + i u)^|k| = A + i B
        A, B = one(P), zero(P)
        for _ in 1:abs(k)
            A, B = A - xpoly(Q) * B, B + xpoly(Q) * A
        end
        A, k < 0 ? -B : B
    end
    # A / (1 + u²)^(k/2)
    function over(A, k::Int)
        iszero(A) && return bd.lift(0)
        k = abs(k)
        r = frac_term(bu, frac(A, w^(k ÷ 2)))
        isodd(k) ? mk(bd, :/, r, rterm) : r
    end
    function back(t)
        if safe_iscall(t) && !isempty(arguments(t))
            n = opname(operation(t))
            args = arguments(t)
            if n in (:sin, :cos, :tan, :cot) && length(args) == 1
                e = radicand_element(args[1], xk)
                if e !== nothing && isone(e.den) && degree(e.num) == 1 && iszero(e.num.c[1])
                    c = e.num.c[2]
                    if isone(denominator(c))
                        k = Int(numerator(c))
                        A, B = cis(k)
                        n === :cos && return over(A, k)
                        n === :sin && return over(B, k)
                        n === :cot && return frac_term(bu, frac(A, B))
                        return frac_term(bu, frac(B, A))
                    elseif c == 1 // 2 && n === :tan    # tan(t/2) = u/(1 + √(1 + u²))
                        return mk(bd, :/, arguments(ats[1])[1], mk(bd, :+, bd.lift(1), rterm))
                    elseif c == 1 // 2 && n === :cot    # cot(t/2) = (1 + √(1 + u²))/u
                        return mk(bd, :/, mk(bd, :+, bd.lift(1), rterm), arguments(ats[1])[1])
                    end
                end
            end
            return term_rebuild(bd, t, Any[back(s) for s in args])
        end
        string(t) == xk ? arcterm : t
    end
    tidy_terms(bd, back(G), xk)
end

# ---------------------------------------------------------------------------
# Step AP: ∫ A·Lᵏ by parts, L = atan(g), asin(g), …, log(g) (a function with an algebraic derivative) and A free
# of L, after the usual route and steps CL, LP and AT have failed (∫ atan(2 tan x), Rubi 206;
# ∫ asin(x)/(1 + x²)^(3/2), Rubi 235): when Q = ∫ A is elementary,
#   ∫ A Lᵏ = Q Lᵏ - k ∫ Q Lᵏ⁻¹ L′,
# both integrals by the usual route (for g rational in sin, cos: step CL; ∫ x log²x/√(x² + 1): k = 2, then dilogarithms
# by steps DL, LF).
# ---------------------------------------------------------------------------
const PARTS = Ref(false)                                # no nested integration by parts
const PARTS_FNS = (:atan, :acot, :asin, :acos, :asec, :acsc, :asinh, :acosh, :atanh, :acoth, :acsch, :asech, :log)

function try_parts(f, x; build = nothing, lift = nothing, verify::Bool = true)
    @nospecialize f x
    PARTS[] && return nothing
    xk = string(x)
    # f = c·Lᵏ·A: one factor L (to a power k ≥ 1, k > 1 for L = log only: asinᵏ(x/a)/√(a² - x²) is step US's), the
    # others free of L; ∫ A Lᵏ = Q Lᵏ - k ∫ Q Lᵏ⁻¹ L′
    fs = product_factors!(Any[], f, 1)
    isL(t, e) = e >= 1 && safe_iscall(t) && (e == 1 || opname(operation(t)) === :log) && opname(operation(t)) in PARTS_FNS && length(arguments(t)) == 1 &&
                depends_on(arguments(t)[1], xk)
    ia = findall(((t, e),) -> isL(t, e), fs)
    isempty(ia) && return nothing
    bd = Builder(build === nothing ? auto_build(f, x) : build, lift === nothing ? auto_lift(f, x) : lift, x)
    for j in ia                                         # (several candidates: each in turn)
        L, k = fs[j]
        Ls = string(L)
        rest = [fs[m] for m in eachindex(fs) if m != j]
        any(((t, _),) -> occursin(Ls, string(t)), rest) && continue
        A = isempty(rest) ? bd.lift(1) :
            mk(bd, :*, (e == 1 ? t : mk(bd, :^, t, bd.lift(e)) for (t, e) in rest)...)
        G = with_parts() do
            Qt = isempty(rest) ? bd.x : risch_integrate(A, x; build = build, lift = lift, verify = verify)
            Qt isa IntegralWithRootSums && return nothing
            dL = term_deriv(bd, L, xk)
            Lk = k == 1 ? L : mk(bd, :^, L, bd.lift(k))
            dLk = k == 1 ? dL : mk(bd, :*, bd.lift(k), k == 2 ? L : mk(bd, :^, L, bd.lift(k - 1)), dL)
            # (one flat product, so that step IT sees a constant factor of Q: b·(…)√(1 + x²)·(1/√(1 + x²)))
            QdL = Any[e == 1 ? t : mk(bd, :^, t, bd.lift(e)) for (t, e) in product_factors!(product_factors!(Any[], Qt, 1), dLk, 1)]
            H = risch_integrate(length(QdL) == 1 ? QdL[1] : mk(bd, :*, QdL...), x; build = build, lift = lift, verify = verify)
            H isa IntegralWithRootSums && return nothing
            mk(bd, :+, mk(bd, :*, Qt, Lk), mk(bd, :*, bd.lift(-1), H))
        end
        # Q and H are each checked, but in the tower log(w) and log(-w) are one generator: the iπ of a log of a
        # negative argument in Q (log(x² - 1) where |x| < 1) is dropped in H's integrand Q L′, where it is not a
        # constant (∫ x³ atanh(x) log(1 - x²)). So G′ = f is checked numerically at real points of f.
        (G !== nothing && verify && !numeric_antiderivative(f, G, xk)) && (G = nothing)
        G === nothing || return G
    end
    nothing
end

# ev(t, x0): the value (ComplexF64) of a term t of the terms ts at x = x0, with the k-th parameter (sorted by
# name) at 0.5 + 0.3k
function numeric_evaluator(xk::String, ts...)
    names = String[]
    function leaves!(t)
        if safe_iscall(t) && !isempty(arguments(t))
            foreach(leaves!, arguments(t))
        else
            s = string(t)
            (s != xk && leaf_rational(t) === nothing && !is_e_const(t) && !(s in ("pi", "π")) && !(s in names)) && push!(names, s)
        end
    end
    foreach(leaves!, ts)
    sort!(names)
    function ev(t, x0)
        if safe_iscall(t) && !isempty(arguments(t))
            return ComplexF64(op_function(t)((ev(a, x0) for a in arguments(t))...))
        end
        s = string(t)
        s == xk && return ComplexF64(x0)
        k = findfirst(==(s), names)
        k === nothing || return ComplexF64(0.5 + 0.3k)
        term_value(t, xk, 0.0)
    end
end

# G′ = f numerically (central differences) at two points where f is real and finite, with the parameters at
# fixed positive values; true when no such points are found or a term cannot be evaluated
function numeric_antiderivative(f, G, xk::String)
    ev = numeric_evaluator(xk, f, G)
    found = 0
    for x0 in (0.13, 0.27, 0.41, 0.58, 0.83, 1.21, 1.77, 2.6, -0.37, -1.4)
        fv, dG = try
            fv = ev(f, x0)
            h = 1e-6 * max(1.0, abs(x0))
            fv, (ev(G, x0 + h) - ev(G, x0 - h)) / (2h)
        catch
            continue
        end
        (isfinite(fv) && isfinite(dG) && abs(imag(fv)) <= 1e-10 * max(1.0, abs(fv))) || continue
        abs(dG - fv) <= 1e-4 * max(1.0, abs(fv)) || return false
        (found += 1) == 2 && return true
    end
    true
end

# f = (s₁ + s₂ + …)·R with a factor that is a sum, one of whose summands has an operation `isop` (a + b asinh x):
# ∫ f = Σ ∫ sᵢ R, each by the usual route (so by parts where sᵢ = b L). Nothing when f has no such factor, or a
# term is refused or not elementary (the terms can cancel; the caller's route then sees f whole).
function distribute_sum_factor(f, x, xk::String, isop; build, lift, verify::Bool)
    @nospecialize f x
    fs = product_factors!(Any[], f, 1)
    hasop(t) = safe_iscall(t) && !isempty(arguments(t)) && (isop(opname(operation(t))) || any(hasop, arguments(t)))
    j = findfirst(((t, e),) -> e == 1 && safe_iscall(t) && opname(operation(t)) === :+ && hasop(t), fs)
    j === nothing && return nothing
    bd = Builder(build === nothing ? auto_build(f, x) : build, lift === nothing ? auto_lift(f, x) : lift, x)
    rest = Any[e == 1 ? t : mk(bd, :^, t, bd.lift(e)) for (i, (t, e)) in enumerate(fs) if i != j]
    Fs = Any[]
    for s in arguments(fs[j][1])
        F = try
            risch_integrate(isempty(rest) ? s : mk(bd, :*, s, rest...), x; build = build, lift = lift, verify = verify)
        catch e
            (e isa RischNotImplemented || e isa NotElementary) || rethrow()
            return nothing
        end
        push!(Fs, F)
    end
    add_answers(bd, Fs, xk)
end

# step SP: a refusal for the number of parameters or constants (the caps on residues and RootSums over
# parameters, MAX_CONSTS), with a factor that is a sum whose summands bring parameters of their own:
# x⁴(c + d x³ + e x⁶)/(a + b x³) = c x⁴/(a + b x³) + …, each term with fewer parameters (step IT takes the
# parameter out of the integral). The factor that leaves the fewest parameters in its largest term; nothing
# when no factor lowers the count, or a term is refused or not elementary (the caller then refuses f).
function split_param_sum(f, x; build, lift, verify::Bool)
    @nospecialize f x
    xk = string(x)
    params(t, acc = Set{String}()) = (safe_iscall(t) && !isempty(arguments(t)) ? foreach(a -> params(a, acc), arguments(t)) :
                                      (has_param(t, xk) && push!(acc, string(t))); acc)
    fs = product_factors!(Any[], f, 1)
    n0 = length(params(f))
    best, bestn = nothing, n0
    for (j, (t, e)) in enumerate(fs)
        (e == 1 && safe_iscall(t) && opname(operation(t)) === :+ && length(arguments(t)) >= 2) || continue
        prest = Set{String}()
        for (i, (u, _)) in enumerate(fs)
            i == j || params(u, prest)
        end
        m = maximum(length(union(prest, params(s))) for s in arguments(t))
        m < bestn && ((best, bestn) = (j, m))
    end
    best === nothing && return nothing
    bd = Builder(build === nothing ? auto_build(f, x) : build, lift === nothing ? auto_lift(f, x) : lift, x)
    rest = Any[e == 1 ? t : mk(bd, :^, t, bd.lift(e)) for (i, (t, e)) in enumerate(fs) if i != best]
    Fs = Any[]
    for s in arguments(fs[best][1])
        F = try
            risch_integrate(isempty(rest) ? s : mk(bd, :*, s, rest...), x; build = build, lift = lift, verify = verify)
        catch e
            (e isa RischNotImplemented || e isa NotElementary) || rethrow()
            return nothing
        end
        push!(Fs, F)
    end
    add_answers(bd, Fs, xk)
end

# run g() with PARTS set; nothing if it is not elementary or not implemented
function with_parts(g)
    PARTS[] = true
    try
        g()
    catch e
        (e isa RischNotImplemented || e isa NotElementary) || rethrow()
        nothing
    finally
        PARTS[] = false
    end
end
