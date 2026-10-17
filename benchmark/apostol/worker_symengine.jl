const T_START = time()
using SymEngine
import RischIntegrate
SymEngine.@vars x t a b c d z n
const VAR = Dict{Symbol,Any}(v => getfield(Main, v) for v in (:x, :t, :a, :b, :c, :d, :z, :n))
INTEGRATE(f, x) = RischIntegrate.integrate(f, x)
SOLVED(out) = true  # failures throw
function EVAL(ex, vals)
    u = SymEngine.N(SymEngine.subs(Basic(ex), (VAR[v] => p for (v, p) in vals)...))
    isa(u, Number) ? complex(u) : nothing
end
include("core.jl")
