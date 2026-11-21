# ---------------------------------------------------------------------------
# Step QW: f = h(x)/E(x²) with E(w) = A₀ + A₂ w + A₄ w² a quadratic over a parameter field (and h holding f's
# radicals, sample 1017: √(1 - x²)/(x² (a + b x² + c x⁴))). With Δ = A₂² - 4A₀A₄ and w± = (-A₂ ± √Δ)/(2A₄) the roots,
#   1/E(x²) = (1/(x² - w₊) - 1/(x² - w₋))/√Δ,
# and ∫ h/(x² - W) dx = G(W) is integrated once, W a new symbol: one parameter where the route through E had three
# (step AS over ℚ(i)(a, b, c): a degree-8 residue resultant, 354 s). Then
#   ∫ f dx = (G(w₊) - G(w₋))/√Δ,
# an identity in W, so it holds for every value of w±, real or not, as for every sign of Δ. Outermost call, before
# step AS; nothing when f has no such factor, G is refused or has a RootSum, or the answer fails the numeric check.
# ---------------------------------------------------------------------------
const QW_NAME = "ϖ"
function integrate_quartic_split(f, x; build = nothing, lift = nothing, verify::Bool = true)
    @nospecialize f x
    xk = string(x)
    has_param(f, xk) || return nothing
    fs = product_factors!(Any[], f, 1)
    # the factor E(x²)^(-1), E with a parameter, even of degree 4 in x
    js = Int[]
    Einfo = nothing
    for (j, (t, e)) in enumerate(fs)
        (e == -1 && depends_on(t, xk) && has_param(t, xk) && isempty(collect_radicals(t, xk))) || continue
        T, el = try
            build_tower(t, xk)
        catch err
            (err isa RischNotImplemented || err isa RischError) || rethrow()
            continue
        end
        (isempty(T.levels) && isone(el.den) && degree(el.num) == 4) || continue
        c = el.num.c
        (iszero(c[2]) && iszero(c[4])) || continue
        real_param_field(ctype(T)) || continue
        push!(js, j)
        Einfo = (T, c[1], c[3], c[5])
    end
    length(js) == 1 || return nothing
    T, A0, A2, A4 = Einfo
    Δ = A2 * A2 - cfromQ(ctype(T), Q(4)) * A0 * A4
    iszero(Δ) && return nothing
    csqrt(Δ) === nothing || return nothing              # (√Δ in the field: E factors, the usual route)
    leaves = Dict{String,Any}()
    collect_leaves!(leaves, f)
    haskey(leaves, QW_NAME) && return nothing
    W = Symbol(QW_NAME)
    hs = Any[e == 1 ? term_to_expr(t) : Expr(:call, :^, term_to_expr(t), e) for (k, (t, e)) in enumerate(fs) if k != js[1]]
    hx = isempty(hs) ? 1 : length(hs) == 1 ? hs[1] : Expr(:call, :*, hs...)
    xs = Symbol(xk)
    g = Expr(:call, :/, hx, Expr(:call, :-, Expr(:call, :^, xs, 2), W))
    G = try
        risch_integrate(g, xs; build = expr_build, lift = identity, verify = verify)
    catch err
        (err isa RischNotImplemented || err isa NotElementary || err isa RischError) || rethrow()
        return nothing
    end
    (G isa IntegralWithRootSums || has_special(G)) && return nothing
    b0 = Builder(build === nothing ? auto_build(f, x) : build, lift === nothing ? auto_lift(f, x) : lift, x, T.consts)
    sΔ = mk(b0, :sqrt, cterm(b0, Δ))
    wterm(σ) = mk(b0, :/, mk(b0, :+, cterm(b0, -A2), σ == 1 ? sΔ : mk(b0, :*, b0.lift(-1), sΔ)),
                  cterm(b0, cfromQ(ctype(T), Q(2)) * A4))
    function back(ex, w)                                # Expr → the user's term type, W ↦ w
        ex === W && return w
        ex isa Symbol && return haskey(leaves, string(ex)) ? leaves[string(ex)] : ex === :ℯ ? mk(b0, :exp, b0.lift(1)) : ex
        ex isa Number && return b0.lift(ex)
        ex isa Expr && ex.head === :call || return ex
        b0.build(op_function(ex), (back(a, w) for a in ex.args[2:end])...)
    end
    F = mk(b0, :/, mk(b0, :+, back(G, wterm(1)), mk(b0, :*, b0.lift(-1), back(G, wterm(-1)))), sΔ)
    (verify && !numeric_antiderivative(f, F, xk)) && return nothing
    F
end
