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
              (opname(operation(t)) === :exp ? false : any(bare, arguments(t))) : string(t) == xk
    hasexp(t) = safe_iscall(t) && !isempty(arguments(t)) &&
                ((opname(operation(t)) === :exp && depends_on(arguments(t)[1], xk)) || any(hasexp, arguments(t)))
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
