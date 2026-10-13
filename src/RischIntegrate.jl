module RischIntegrate

# Write your package code here.
include("Risch.jl")
export integrate

integrate(ex, x) = Risch.risch_integrate(ex, x)

"""
    integrate(ex, x, ys...)

Indefinite integral of a symbolic expression over variable x. Iterative integrals are possible.
"""
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
