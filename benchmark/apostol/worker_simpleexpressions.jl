const T_START = time()
using SimpleExpressions
import RischIntegrate
SimpleExpressions.@symbolic_variables x t a b c d z n
Base.://(a::SimpleExpressions.AbstractSymbolic, b::Int64) = a / b   # as in test/test_apostol.jl
const VAR = Dict{Symbol,Any}(v => getfield(Main, v) for v in (:x, :t, :a, :b, :c, :d, :z, :n))
INTEGRATE(f, x) = RischIntegrate.integrate(f, x)
SOLVED(out) = true  # failures throw
# evaluate by replacing each variable, then calling the constant expression
function EVAL(ex, vals)
    isa(ex, Number) && return complex(ex)
    u = replace(ex, (VAR[v] => p for (v, p) in vals)...)()
    isa(u, Number) ? complex(u) : nothing
end
include("core.jl")
