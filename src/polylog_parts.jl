# ---------------------------------------------------------------------------
# Step LP: ∫ c logʲ(x) L(w x)/x, L a polylogarithm of a multiple of x, after the usual route has failed
# (∫ atan(x) log(x)/x, Rubi 207). With Liₙ′(w x) = Liₙ₋₁(w x)/x, by parts
#   ∫ logʲ(x) Liₙ(w x)/x = Σ_{l=0..j} (-1)ˡ j!/(j-l)! log^(j-l)(x) Li_{n+1+l}(w x),
# and L is one of
#   atan(c x) = Im Li₁(i c x),   log(a + b x) = log a - Li₁(-(b/a) x) (a > 0),   li2(c x) = Li₂(c x),
# printed with impolylog(m, c x, π/2) = Im Liₘ(i c x), li2 and repolylog(m, y, 0) = Liₘ(y) (y < 1).
# ---------------------------------------------------------------------------

# the factors of a product t^e as (factor, exponent) pairs
function product_factors!(out, t, e::Int)
    if safe_iscall(t) && !isempty(arguments(t))
        n, args = opname(operation(t)), arguments(t)
        n === :* && return (foreach(a -> product_factors!(out, a, e), args); out)
        n === :/ && length(args) == 2 && return (product_factors!(out, args[1], e); product_factors!(out, args[2], -e); out)
        if n === :^ && length(args) == 2
            p = leaf_rational(args[2])
            p !== nothing && isone(denominator(p)) && return product_factors!(out, args[1], e * Int(numerator(p)))
        end
    end
    push!(out, (t, e))
end

function try_log_polylog(f, x; build = nothing, lift = nothing, verify::Bool = true)
    @nospecialize f x
    xk = string(x)
    isx(t) = !safe_iscall(t) && string(t) == xk
    c, xe, j, L = Q(1), 0, 0, nothing
    for (t, e) in product_factors!(Any[], f, 1)
        r = leaf_rational(t)
        if r !== nothing
            c *= Q(r)^e
        elseif isx(t)
            xe += e
        elseif safe_iscall(t) && length(arguments(t)) == 1
            n, a = opname(operation(t)), arguments(t)[1]
            if n === :log && isx(a)
                j += e
                continue
            end
            (e == 1 && L === nothing && n in (:atan, :log, :li2)) || return nothing
            u = radicand_element(a, xk)
            (u !== nothing && isone(u.den) && degree(u.num) == 1) || return nothing
            a0, a1 = u.num.c[1] / u.den.c[1], u.num.c[2] / u.den.c[1]
            if n === :log
                a0 > 0 || return nothing
                L = (:log, -a1 / a0, a0)                # log(a0 + a1 x) = log a0 - Li₁(-(a1/a0) x)
            else
                iszero(a0) || return nothing
                L = (n, a1, Q(1))
            end
        else
            return nothing
        end
    end
    (xe == -1 && j >= 0 && L !== nothing) || return nothing
    kind, w, a0 = L
    n = kind === :li2 ? 2 : 1
    bd = Builder(build === nothing ? auto_build(f, x) : build, lift === nothing ? auto_lift(f, x) : lift, x)
    sc(q, t) = isone(q) ? t : mk(bd, :*, cterm(bd, q), t)
    wx(q) = isone(q) ? bd.x : mk(bd, :*, cterm(bd, q), bd.x)
    lx = mk(bd, :log, bd.x)
    lxp(p) = p == 0 ? nothing : p == 1 ? lx : mk(bd, :^, lx, bd.lift(p))
    # (sign, Liₘ term): Liₘ(w x) for li2, -Liₘ(w x) for log, Im Liₘ(i w x) for atan
    function polylog(m)
        kind === :atan && return (1, mk(bd, :ImLi, bd.lift(m), wx(w), mk(bd, :*, cterm(bd, Q(1, 2)), bd.lift(π))))
        t = m == 2 ? mk(bd, :li2, wx(w)) : mk(bd, :ReLi, bd.lift(m), wx(w), bd.lift(0))
        (kind === :log ? -1 : 1, t)
    end
    terms = Any[]
    for l in 0:j
        s, t = polylog(n + 1 + l)
        q = c * s * (-1)^l * Q(factorial(j) ÷ factorial(j - l))
        p = lxp(j - l)
        push!(terms, sc(q, p === nothing ? t : mk(bd, :*, p, t)))
    end
    if kind === :log && !isone(a0)                      # ∫ c log(a0) logʲ(x)/x = c log(a0) log^(j+1)(x)/(j+1)
        push!(terms, mk(bd, :*, cterm(bd, c / (j + 1)), mk(bd, :log, cterm(bd, a0)), lxp(j + 1)))
    end
    length(terms) == 1 ? terms[1] : mk(bd, :+, terms...)
end

# Step PX: f = Σₖ xᵏ gₖ, x elsewhere only inside the arguments of functions, with a radical refused for its
# radicand (x/csc(x)^(3/2) - x √csc(x)/3, Rubi 1354: each summand an elliptic integral, the sum is not), by parts
# from the top power down: ∫ xⁿ gₙ = xⁿ Gₙ - n ∫ xⁿ⁻¹ Gₙ, Gₙ = ∫ gₙ, so -n Gₙ joins gₙ₋₁; the answer is Σ xᵏ Gₖ with
# Gₖ = ∫ (gₖ - (k + 1) Gₖ₊₁). Each ∫ at the caller's depth (its radical fallbacks, step HT); nothing when one is
# refused or has RootSums.
const PXPARTS = Ref(false)                              # no nested step PX
has_op_in(t, ns) = safe_iscall(t) && !isempty(arguments(t)) && (opname(operation(t)) in ns || any(a -> has_op_in(a, ns), arguments(t)))
const PX_FUNCS = (:sin, :cos, :tan, :cot, :sec, :csc, :sinh, :cosh, :tanh, :coth, :sech, :csch, :exp, :log)
# G = 0 at three generic points (b⁻¹·0, a coefficient's integral that cancels), parameters at `numeric_evaluator`'s values
function numeric_zero(G, xk::String)
    ev = try numeric_evaluator(xk, G) catch; return false end
    all(x0 -> (v = try ev(G, x0) catch; NaN end; isfinite(v) && abs(v) < 1e-13), (0.41, 1.21, 0.27))
end
function try_poly_radical_parts(f, x; build = nothing, lift = nothing, verify::Bool = true)
    @nospecialize f x
    PXPARTS[] && return nothing
    xk = string(x)
    isx(t) = !safe_iscall(t) && string(t) == xk
    # x bare: outside the arguments of the trigonometric, hyperbolic, exponential and logarithmic functions (x in a
    # radicand, √(1 + x²), is bare: Apostol 19 is no case for step PX)
    bare(t) = isx(t) || (safe_iscall(t) && !isempty(arguments(t)) && !(opname(operation(t)) in PX_FUNCS) &&
                         any(bare, arguments(t)))
    bd = Builder(build === nothing ? auto_build(f, x) : build, lift === nothing ? auto_lift(f, x) : lift, x)
    pw(t, e) = e == 1 ? t : mk(bd, :^, t, bd.lift(e))
    function summands(u, sg, out)
        if safe_iscall(u) && opname(operation(u)) === :+
            foreach(a -> summands(a, sg, out), arguments(u))
        elseif safe_iscall(u) && opname(operation(u)) === :- && length(arguments(u)) == 2
            summands(arguments(u)[1], sg, out); summands(arguments(u)[2], -sg, out)
        elseif safe_iscall(u) && opname(operation(u)) === :- && length(arguments(u)) == 1
            summands(arguments(u)[1], -sg, out)
        else
            push!(out, (u, sg))
        end
        out
    end
    C = Dict{Int,Vector{Any}}()
    for (t, sg) in summands(f, 1, Tuple{Any,Int}[])
        k, gs = 0, Any[]
        for (u, e) in product_factors!(Any[], t, 1)
            if isx(u)
                e >= 0 || return nothing
                k += e
            else
                bare(u) && return nothing
                push!(gs, pw(u, e))
            end
        end
        sg == -1 && pushfirst!(gs, bd.lift(-1))
        push!(get!(C, k, Any[]), isempty(gs) ? bd.lift(1) : length(gs) == 1 ? gs[1] : mk(bd, :*, gs...))
    end
    n = maximum(keys(C))
    n >= 1 || return nothing
    any(gs -> any(g -> !isempty(collect_radicals(g, xk)) && has_op_in(g, RM_FUNCS), gs), values(C)) || return nothing
    PXPARTS[] = true
    try
        out = Any[]
        carry = nothing
        for k in n:-1:0
            gs = copy(get(C, k, Any[]))
            carry === nothing || push!(gs, carry)
            if isempty(gs)
                carry = nothing
                continue
            end
            g = length(gs) == 1 ? gs[1] : mk(bd, :+, gs...)
            G = as_outer(() -> risch_integrate(g, x; build = build, lift = lift, verify = verify))
            G isa IntegralWithRootSums && return nothing
            if leaf_rational(G) == 0 || numeric_zero(G, xk)
                carry = nothing
                continue
            end
            push!(out, k == 0 ? G : mk(bd, :*, pw(bd.x, k), G))
            carry = k == 0 ? nothing : mk(bd, :*, bd.lift(-k), G)
        end
        isempty(out) ? bd.lift(0) : length(out) == 1 ? out[1] : mk(bd, :+, out...)
    catch err
        (err isa RischNotImplemented || err isa NotElementary) || rethrow()
        nothing
    finally
        PXPARTS[] = false
    end
end

# Step XP: ∫ P(x) R(e^(kx)) not elementary (P a polynomial, R rational in exponentials of x with x nowhere else:
# x/(eˣ - 1), SymPy #30167), by parts with Q = ∫ R elementary: P Q - ∫ P′ Q, the second integral by the usual
# route (∫ log(1 - eˣ) = -Li₂(eˣ), step 8a). ∫ x/(eˣ - 1) = x (log(eˣ - 1) - x) + x²/2 - ∫ log(eˣ - 1).
# Nothing when f is not of that kind or a part is refused.
const XPARTS = Ref(false)                               # no nested step XP
function try_poly_exp_parts(f, x; build = nothing, lift = nothing, verify::Bool = true)
    @nospecialize f x
    XPARTS[] && return nothing
    xk = string(x)
    # x only inside exp
    bare(t) = safe_iscall(t) && !isempty(arguments(t)) ?
              (exp_arg(t) !== nothing ? false : any(bare, arguments(t))) : string(t) == xk
    hasexp(t) = safe_iscall(t) && !isempty(arguments(t)) &&
                ((exp_arg(t) !== nothing && depends_on(exp_arg(t), xk)) || any(hasexp, arguments(t)))
    bd = Builder(build === nothing ? auto_build(f, x) : build, lift === nothing ? auto_lift(f, x) : lift, x)
    pw(t, e) = e == 1 ? t : mk(bd, :^, t, bd.lift(e))
    Ps, Rs = Any[], Any[]
    for (t, e) in product_factors!(Any[], f, 1)
        if hasexp(t)
            bare(t) && return nothing
            push!(Rs, pw(t, e))
        elseif depends_on(t, xk)
            e >= 1 || return nothing
            T, el = try                                 # a polynomial in x
                build_tower(t, xk)
            catch err
                (err isa RischNotImplemented || err isa RischError) || rethrow()
                return nothing
            end
            (isempty(T.levels) && degree(el.den) == 0) || return nothing
            push!(Ps, pw(t, e))
        else
            push!(Ps, pw(t, e))
        end
    end
    (isempty(Rs) || !any(t -> depends_on(t, xk), Ps)) && return nothing
    P = length(Ps) == 1 ? Ps[1] : mk(bd, :*, Ps...)
    R = length(Rs) == 1 ? Rs[1] : mk(bd, :*, Rs...)
    # (step AP stays on: ∫ log(eˣ - 1) is its)
    XPARTS[] = true
    try
        Qt = risch_integrate(R, x; build = build, lift = lift, verify = verify)
        Qt isa IntegralWithRootSums && return nothing
        # P′ Q with P′ distributed over the summands of Q (the dilogarithm step takes log(1 + eˣ) as a summand)
        dP = term_deriv(bd, P, xk)
        qs = (safe_iscall(Qt) && opname(operation(Qt)) === :+) ? arguments(Qt) : Any[Qt]
        one_ = leaf_rational(dP) == 1
        hs = Any[one_ ? q : mk(bd, :*, dP, q) for q in qs]
        H = risch_integrate(length(hs) == 1 ? hs[1] : mk(bd, :+, hs...), x; build = build, lift = lift, verify = verify)
        H isa IntegralWithRootSums && return nothing
        mk(bd, :+, mk(bd, :*, P, Qt), mk(bd, :*, bd.lift(-1), H))
    catch err
        (err isa RischNotImplemented || err isa NotElementary) || rethrow()
        nothing
    finally
        XPARTS[] = false
    end
end
