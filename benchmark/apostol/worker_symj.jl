const T_START = time()
using SymJ, SpecialFunctions, PolyLog, HypergeometricFunctions
import RischIntegrate
const VAR = Dict{Symbol,Any}(v => Sym(v) for v in (:x, :t, :a, :b, :c, :d, :z, :n))
INTEGRATE(f, x) = RischIntegrate.integrate(f, x)
SOLVED(out) = true  # failures throw
# substitute the numbers, then evaluate the constant expression
function EVAL(ex, vals)
    u = N(subs(ex, (VAR[v] => p for (v, p) in vals)...))
    isa(u, Number) ? complex(u) : nothing
end
include("core.jl")
