const T_START = time()
import RischIntegrate
include("giac_common.jl")
INTEGRATE(f, x) = RischIntegrate.integrate(f, x)
SOLVED(out) = true  # failures throw
include("core.jl")
