# ---------------------------------------------------------------------------
# Step QW: f = h/E(g) with E(w) = A₀ + A₁ w + A₂ w² a quadratic over a parameter field and g = x² (E(x²) an even quartic;
# h holding f's radicals, sample 1017: √(1 - x²)/(x² (a + b x² + c x⁴))) or g a function of x (sin L, cos L, …;
# sample 1536: sec²x/(a + b sin x + c sin²x)). With Δ = A₁² - 4A₀A₂ and w± = (-A₁ ± √Δ)/(2A₂) the roots,
#   1/E(g) = (1/(g - w₊) - 1/(g - w₋))/√Δ,
# and ∫ h/(g - W) dx = G(W) is integrated once, W a new symbol: one parameter where the route through E had three
# (step AS over ℚ(i)(a, b, c) for 1017: a degree-8 residue resultant, 354 s). Then
#   ∫ f dx = (G(w₊) - G(w₋))/√Δ,
# an identity in W, so it holds for every value of w±, real or not, as for every sign of Δ. Outermost call; for a
# function g only with three or more parameters in E (where the resultants over them do not finish), so that the
# usual routes keep the integrands they take. Nothing when f has no such factor, G is refused or has a RootSum,
# or the answer fails the numeric check.
# ---------------------------------------------------------------------------
const QW_NAME = "ϖ"
const QW_KERNEL = "ϖY"
const QW_FUNS = (:sin, :cos, :tan, :cot, :sec, :csc, :sinh, :cosh, :tanh, :coth, :exp, :log)

# E(g) in the factor t: (g as an Expr, A₀, A₁, A₂, the tower over E's constants), or nothing
function qw_quadratic(t, xk::String; kernel::Symbol)
    if kernel === :square
        T, el = try
            build_tower(t, xk)
        catch err
            (err isa RischNotImplemented || err isa RischError) || rethrow()
            return nothing
        end
        (isempty(T.levels) && isone(el.den) && degree(el.num) == 4) || return nothing
        c = el.num.c
        (iszero(c[2]) && iszero(c[4])) || return nothing
        real_param_field(ctype(T)) || return nothing
        return (Expr(:call, :^, Symbol(xk), 2), c[1], c[3], c[5], T)
    end
    te = term_to_expr(t)
    gs = Any[]
    function walk(e)
        e isa Expr && e.head === :call || return
        if e.args[1] in QW_FUNS && length(e.args) == 2 && has_x(e.args[2], xk)
            any(g -> g == e, gs) || push!(gs, e)
            return
        end
        foreach(walk, e.args[2:end])
    end
    walk(te)
    Y = Symbol(QW_KERNEL)
    for g in gs
        tY = expr_replace(te, g, Y)
        has_x(tY, xk) && continue
        T, el = try
            build_tower(tY, QW_KERNEL)
        catch err
            (err isa RischNotImplemented || err isa RischError) || rethrow()
            continue
        end
        (isempty(T.levels) && isone(el.den) && degree(el.num) == 2) || continue
        real_param_field(ctype(T)) || continue
        count(c -> c.kind === :sym, T.consts) >= 3 || continue
        c = el.num.c
        return (g, c[1], c[2], c[3], T)
    end
    nothing
end
expr_replace(e, a, b) = e == a ? b : e isa Expr ? Expr(e.head, (expr_replace(s, a, b) for s in e.args)...) : e

function integrate_quartic_split(f, x; build = nothing, lift = nothing, verify::Bool = true, kernel::Symbol = :square)
    @nospecialize f x
    xk = string(x)
    has_param(f, xk) || return nothing
    fs = product_factors!(Any[], f, 1)
    found = nothing
    for (j, (t, e)) in enumerate(fs)
        (e == -1 && depends_on(t, xk) && has_param(t, xk) && isempty(collect_radicals(t, xk))) || continue
        q = qw_quadratic(t, xk; kernel = kernel)
        q === nothing && continue
        found === nothing || return nothing             # (two such factors: not this step)
        found = (j, q)
    end
    found === nothing && return nothing
    j, (gk, A0, A1, A2, T) = found
    Δ = A1 * A1 - cfromQ(ctype(T), Q(4)) * A0 * A2
    iszero(Δ) && return nothing
    csqrt(Δ) === nothing || return nothing              # (√Δ in the field: E factors, the usual route)
    leaves = Dict{String,Any}()
    collect_leaves!(leaves, f)
    (haskey(leaves, QW_NAME) || haskey(leaves, QW_KERNEL)) && return nothing
    W = Symbol(QW_NAME)
    hs = Any[e == 1 ? term_to_expr(t) : Expr(:call, :^, term_to_expr(t), e) for (k, (t, e)) in enumerate(fs) if k != j]
    hx = isempty(hs) ? 1 : length(hs) == 1 ? hs[1] : Expr(:call, :*, hs...)
    xs = Symbol(xk)
    g = Expr(:call, :/, hx, Expr(:call, :-, gk, W))
    G = try
        risch_integrate(g, xs; build = expr_build, lift = identity, verify = verify)
    catch err
        (err isa RischNotImplemented || err isa NotElementary || err isa RischError) || rethrow()
        return nothing
    end
    (G isa IntegralWithRootSums || has_special(G)) && return nothing
    b0 = Builder(build === nothing ? auto_build(f, x) : build, lift === nothing ? auto_lift(f, x) : lift, x, T.consts)
    sΔ = mk(b0, :sqrt, cterm(b0, Δ))
    wterm(σ) = mk(b0, :/, mk(b0, :+, cterm(b0, -A1), σ == 1 ? sΔ : mk(b0, :*, b0.lift(-1), sΔ)),
                  cterm(b0, cfromQ(ctype(T), Q(2)) * A2))
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
