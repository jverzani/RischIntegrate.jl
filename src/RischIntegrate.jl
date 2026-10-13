"""
    RischIntegrate

This is

> Symbolic integration following Bronstein, *Symbolic Integration I: Transcendental Functions*, for any symbolic term type that implements the TermInterface.jl methods `iscall`, `operation` and `arguments` (SimpleExpressions.jl, SymEngine.jl, `Expr`, ...). Nothing else is required: all algebra is done by this module's own exact, dependency-free polynomial / rational-function types, and results are rebuilt by calling operations as functions.

This was completely implemented by Claude Code, which presumably had "read" the book.

The repository https://github.com/JuliaSymbolics/SymbolicIntegration.jl was not consulted. It too has an implementation of the algorithm, but is loosely coupled with Symbolics.

"""
module RischIntegrate

# Write your package code here.
include("Risch.jl")
export integrate

"""
    integrate(ex, x, ys...)

Indefinite integral of a symbolic expression over variable x. Iterative integrals are possible.
"""
integrate(ex, x) = Risch.risch_integrate(ex, x)

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

end
