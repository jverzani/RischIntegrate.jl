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
