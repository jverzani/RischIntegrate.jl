const T_START = time()
import RischIntegrate
using SpecialFunctions, PolyLog   # for evaluating answers with expinti, li2, ...
const VAR = Dict{Symbol,Any}(v => v for v in (:x, :t, :a, :b, :c, :d, :z, :n))
const OPTS = (build = (op, args...) -> Expr(:call, nameof(op), args...), lift = identity)
INTEGRATE(f, x) = RischIntegrate.integrate(f, x; OPTS...)
SOLVED(out) = true  # failures throw
BUILD(ex) = ex      # the problem's quoted expression is the integrand
# evaluate by replacing each variable with its value, then evaluating the Expr
subst(ex, vals) = ex isa Symbol ? get(vals, ex, ex) :
    ex isa Expr ? Expr(ex.head, (subst(a, vals) for a in ex.args)...) : ex
function EVAL(ex, vals)
    u = Core.eval(Main, subst(ex, vals))
    isa(u, Number) ? complex(u) : nothing
end
include("core.jl")
