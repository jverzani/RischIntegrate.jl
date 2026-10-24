"""
    RischIntegrate

$(replace(read(joinpath(@__DIR__, "..", "README.md"), String), "```julia" => "```jldoctest readme"))

"""
module RischIntegrate

# Write your package code here.
using TermInterface: iscall, operation, arguments, maketerm
using SpecialFunctions: expinti, sinint, cosint, erf, erfi
using PolyLog: li2
import PolyLog
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
include("hyperelliptic.jl")
include("kummer.jl")
include("rootsum.jl")
include("tower_real_forms.jl")
include("tower_rootsums.jl")
include("rootsum_numerics.jl")
include("bioche.jl")
include("sturm.jl")
include("inverse_trig.jl")
include("u_substitution.jl")
include("risch_integrate.jl")
include("biquadratic.jl")
include("denest.jl")
include("nested.jl")
include("hypergeometric.jl")
include("gamma_terms.jl")
include("param_radicals.jl")
include("clausen.jl")
include("polylog_parts.jl")
include("hyp_symbolic.jl")
include("special_fallback.jl")
include("monomial_radicals.jl")
include("kummer_logs.jl")
include("real_log_arguments.jl")

export integrate, sinhint, coshint, clausen2, clausen, repolylog, impolylog

"""
    integrate(ex, x, ys...; build = nothing, lift = nothing)

Indefinite integral of a symbolic expression over variable x. Iterative integrals are possible.

The keywords control how the answer is rebuilt as a term: `build(op, args...)` makes the term
for the operation `op` (a function such as `+`, `sqrt` or `log`) applied to `args`, and `lift(n)`
turns a Julia number into a term. By default operations are called as functions (for
SymbolicUtils terms, constants such as `sqrt(2)` are built with `TermInterface.maketerm`). See the
README for SymbolicUtils.jl and Symbolics.jl.
"""
# (@nospecializeinfer: a call from compiled code, such as the definite integral below or a user's function,
# is inferred with the argument types as declared, not through the whole integrator for the term type)
Base.@nospecializeinfer integrate(@nospecialize(ex), @nospecialize(x); kw...) = risch_integrate(ex, x; kw...)

function integrate(ex, a, bs...; kw...)
    f = integrate(ex, a; kw...)
    for b in bs
        f = integrate(f, b; kw...)
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
function integrate(ex, xabs::Tuple...; kw...)
    val = ex
    for (x, a, b) in xabs
        ∫f = integrate(val, x; kw...)
        val = ∫f(x=>b) - ∫f(x=>a)
    end
    val
end

include("precompile.jl")

end
