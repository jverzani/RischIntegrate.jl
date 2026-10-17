const T_START = time()
include("giac_common.jl")
INTEGRATE(f, x) = invoke_cmd(:integrate, f, x)
SOLVED(out) = !occursin("integrate", string(out))  # Giac leaves what it can not do unevaluated
include("core.jl")
