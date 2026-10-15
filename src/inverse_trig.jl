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

has_op(f, n::Symbol) = safe_iscall(f) && !isempty(arguments(f)) &&
                       (opname(operation(f)) === n || any(a -> has_op(a, n), arguments(f)))
# step AC: acot(u) ↦ atan(1/u) (Julia's definition, all u ≠ 0)
function rewrite_acot(f, x, build, lift)
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

# [(kind, argument term, whole term)] of the asin / acos / acsc / asec subterms of f
function collect_arcs(f, xk::String, out = Any[])
    if safe_iscall(f)
        args = arguments(f)
        n = opname(operation(f))
        n in (:asin, :acos, :acsc, :asec) && length(args) == 1 && push!(out, (n, args[1], f))
        for a in args
            collect_arcs(a, xk, out)
        end
    end
    out
end

# rebuild a term with its arguments mapped (operations called as functions, as in `term_value`)
function term_rebuild(b::Builder, t, args)
    b.build(op_function(t), args...)
end

function integrate_arcsin(f, x, arcs; sK::Q = Q(1), radicand = nothing, build = nothing, lift = nothing,
                          verify::Bool = true)
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
    # recip (s = 1/u): √(1 - 1/u²) = √(u² - 1)/u (u > 0)
    rterm = recip ? mk(bd, :/, mk(bd, :sqrt, poly_term(bu, P(Q[-1, 0, 1]))), arcs[1][2]) :
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
            if n in (:sin, :cos, :tan) && length(args) == 1
                e = radicand_element(args[1], xk)
                if e !== nothing && isone(e.den) && degree(e.num) == 1 && iszero(e.num.c[1])
                    c = e.num.c[2]
                    if isone(denominator(c))
                        cc, sn = cis(Int(numerator(c)))
                        n === :sin && return pterm(sn)
                        n === :cos && return pterm(cc)
                        return mk(bd, :/, pterm(sn), pterm(cc))
                    elseif c == 1 // 2 && n === :tan          # tan(t/2) = sin t/(1 + cos t)
                        return mk(bd, :/, pterm(csin), mk(bd, :+, bd.lift(1), pterm(ccos)))
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
