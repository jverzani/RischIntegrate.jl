using RischIntegrate
using Test

# the decision tests expect NotElementary; ₂F₁ answers (phase 6) are switched on in their own testset
RischIntegrate.HYP_ANSWERS[] = false

# RISCH_TEST_TYPES=one (CI, all jobs but the coverage one): the testsets that run once per term type run
# with SimpleExpressions only, not again with SymEngine
const ALL_TYPES = get(ENV, "RISCH_TEST_TYPES", "all") != "one"

include("test_integrate.jl")
include("test_trig.jl")
include("test_risch.jl")
include("test_tower.jl")
include("test_constants.jl")
include("test_symbolicutils.jl")
include("test_apostol.jl")
