using RischIntegrate
using Test

# the decision tests expect NotElementary; ₂F₁ answers (phase 6) are switched on in their own testset
RischIntegrate.HYP_ANSWERS[] = false

include("test_integrate.jl")
include("test_trig.jl")
include("test_risch.jl")
include("test_tower.jl")
include("test_constants.jl")
include("test_apostol.jl")
include("test_compile.jl")
