"""
    RischIntegrate

$(replace(read(joinpath(@__DIR__, "..", "README.md"), String), "```julia" => "```jldoctest readme"))

"""
module RischIntegrate

# Write your package code here.
using TermInterface: iscall, operation, arguments
using SpecialFunctions: expinti, sinint, cosint, erf, erfi
using PolyLog: li2
using PrecompileTools: @setup_workload, @compile_workload

include("core.jl")
include("polynomials.jl")
include("fractions.jl")
include("factoring.jl")
include("number_fields.jl")
include("hermite_reduction.jl")
include("rothstein_trager.jl")
include("log_to_atan.jl")
include("quartic_residues.jl")
include("term_input.jl")
include("term_output.jl")
include("tower.jl")
include("constant_fields.jl")
include("structure_theorems.jl")
include("tower_terms.jl")
include("rde_base.jl")
include("risch_de.jl")
include("parametric_rde.jl")
include("monomial_integration.jl")
include("dilogarithms.jl")
include("exp_trig_polynomials.jl")
include("special_functions.jl")
include("real_form.jl")
include("radicals.jl")
include("euler_substitutions.jl")
include("rootsum.jl")
include("tower_real_forms.jl")
include("tower_rootsums.jl")
include("rootsum_numerics.jl")
include("bioche.jl")
include("sturm.jl")
include("inverse_trig.jl")
include("u_substitution.jl")
include("risch_integrate.jl")
include("real_log_arguments.jl")

export integrate

"""
    integrate(ex, x, ys...)

Indefinite integral of a symbolic expression over variable x. Iterative integrals are possible.
"""
integrate(ex, x) = risch_integrate(ex, x)

function integrate(ex, a, bs...)
    f = integrate(ex, a)
    for b in bs
        f = integrate(f, b)
    end
    f
end

"""
    integrate(ex, xabs::Tuple)

Definite integral of a symbolic expression over variable `x` from `a` to `b`.

## Example
```julia
@symbolic x
out = integrate(sin(x), (x, 0, pi))
out, simplify(out)
```
"""
function integrate(ex, xabs::Tuple...)
    val = ex
    for (x, a, b) in xabs
        ∫f = integrate(val, x)
        val = ∫f(x=>b) - ∫f(x=>a)
    end
    val
end

include("precompile.jl")

end
