# ---------------------------------------------------------------------------
# A front end for Julia expressions: `@integrate` (not exported), as GruntzLimit's `@limit`
# ---------------------------------------------------------------------------
expr_build(op, args...) = Expr(:call, nameof(op), args...)

"""
    RischIntegrate.@integrate(f, x)
    RischIntegrate.@integrate(f, x, y, …)
    RischIntegrate.@integrate(f, (x, a, b), …)
    RischIntegrate.@integrate(f, x…, key = value…)

The integral of the expression `f`, written without quoting: a convenience front end to
[`integrate`](@ref) for Julia `Expr`s, so no symbolic package is needed. `f` is taken as an `Expr`
in the variables, which are names; other names in `f` are parameters. Use `\$v` to put in the
value of a variable `v`. The bounds `a`, `b` and the keyword values are evaluated as usual.

* `x`: the indefinite integral, an `Expr` (or an [`IntegralWithRootSums`](@ref
  RischIntegrate.IntegralWithRootSums));
* `x, y, …`: iterated, ∫ … (∫ f dx) dy …;
* `(x, a, b)`: definite, F(b) - F(a): a number when it evaluates to one, else an `Expr` (with
  parameters, or symbolic bounds);
* the keywords are passed on: `build` (default `(op, args...) -> Expr(:call, nameof(op), args...)`),
  `lift` (default `identity`), `verify`.

```julia
import RischIntegrate: @integrate
@integrate(x * exp(x), x)          # (-1 + x) * exp(x)
@integrate(sin(x), (x, 0, π))      # 2.0
@integrate(x^2 * y, x, y)          # (1//3 * x ^ 3) * (1//2 * y ^ 2)
@integrate(a * x^2, (x, 0, 1))     # a * (1//3 * 1 ^ 3) - a * (1//3 * 0 ^ 3): a parameter, an Expr
n = 3; @integrate(x^\$n, x)         # 1//4 * x ^ 4
@integrate(sin(x), (x, 0, :b))     # -1 * cos(b) - -1 * cos(0): a symbolic bound, quoted
```
"""
macro integrate(f, args...)
    specs, kws = Any[], Any[]
    for a in args
        if a isa Symbol
            push!(specs, QuoteNode(a))
        elseif a isa Expr && a.head === :tuple && length(a.args) == 3 && a.args[1] isa Symbol
            push!(specs, :(($(QuoteNode(a.args[1])), $(esc(a.args[2])), $(esc(a.args[3])))))
        elseif a isa Expr && a.head === :(=) && a.args[1] isa Symbol
            push!(kws, Expr(:kw, a.args[1], esc(a.args[2])))
        else
            throw(ArgumentError("@integrate: after the integrand, only variable names `x`, bounds `(x, a, b)` " *
                                "and `key = value` arguments are allowed; got `$a`"))
        end
    end
    isempty(specs) && throw(ArgumentError("@integrate: give the variable of integration, `x` or `(x, a, b)`"))
    # quoting (not a QuoteNode) lets `$v` put in the value of `v`
    :(integrate_expr($(esc(Expr(:quote, f))), $(specs...); $(kws...)))
end

function integrate_expr(f, specs...; build = expr_build, lift = identity, verify::Bool = true)
    val = f
    for s in specs
        if s isa Symbol
            val = risch_integrate(val, s; build = build, lift = lift, verify = verify)
        else
            x, a, b = s
            F = risch_integrate(val, x; build = build, lift = lift, verify = verify)
            val = definite_value(F, x, a, b)
        end
    end
    val
end

# F(b) - F(a): a number when both evaluate to numbers, else an Expr
function definite_value(F, x::Symbol, a, b)
    if F isa IntegralWithRootSums
        v = F(b) - F(a)
        return abs(imag(v)) <= 1e-12 * max(1, abs(v)) ? real(v) : v
    end
    xk = string(x)
    subst(e, v) = e isa Symbol ? (e === x ? v : e) : e isa Expr ? Expr(e.head, (subst(t, v) for t in e.args)...) : e
    v = try
        b isa Number && a isa Number ? expr_value(F, xk, b) - expr_value(F, xk, a) : nothing
    catch err
        err isa RischError || rethrow()
        nothing                                         # (a parameter in F)
    end
    v === nothing && return :($(subst(F, b)) - $(subst(F, a)))
    abs(imag(v)) <= 1e-12 * max(1, abs(v)) ? real(v) : v
end
