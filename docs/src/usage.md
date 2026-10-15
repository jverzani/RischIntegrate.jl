# Usage

```julia
integrate(ex, x)                 # indefinite integral
integrate(ex, x, y, …)           # iterated: ∫ … (∫ ex dx) dy …
integrate(ex, (x, a, b), …)      # definite: F(b) - F(a)
```

The answer is a term of the same package as `ex` (without a constant of integration), or an
[`IntegralWithRootSums`](@ref RischIntegrate.IntegralWithRootSums) when the logarithmic part needs the roots of a polynomial of degree
greater than 2.

```@setup latex
# show the answers of the examples as typeset math
using Latexify, SymEngine, SimpleExpressions, SymbolicUtils
for T in (SymEngine.Basic, SimpleExpressions.AbstractSymbolic, SymbolicUtils.BasicSymbolic)
    @eval Base.show(io::IO, ::MIME"text/latex", ex::$T) =
        print(io, latexify(replace(string(ex), r"\b[A-Za-z]\w*\." => ""); cdot = false))   # SpecialFunctions.erf → erf
end
```

## SymEngine.jl

```@example symengine
using SymEngine: @vars
using RischIntegrate: integrate
@vars x y

integrate(x * exp(x), x)
```

```@example symengine
integrate(1 / (1 + cos(x)^2), x)          # continuous on the whole real line
```

```@example symengine
integrate(sqrt(x) / (x - 1), x)           # radicals by substitution
```

```@example symengine
integrate(x * y, x, y)                     # iterated
```

## SimpleExpressions.jl

```@example simpleexpressions
using SimpleExpressions
using RischIntegrate: integrate
@symbolic x

integrate(log(x)^2, x)
```

```@example simpleexpressions
integrate(1 / (x * sqrt(x^2 + 1)), x)
```

## SymbolicUtils.jl

SymbolicUtils terms implement the TermInterface methods and are integrated directly. Constants
such as `sqrt(2)` are kept exact (they are built with `TermInterface.maketerm`; SymbolicUtils
would otherwise evaluate `sqrt(2)` to a floating point number):

```@example symbolicutils
using SymbolicUtils: @syms
using RischIntegrate: RischIntegrate, integrate
@syms x::Real a::Real

integrate(1 / (x^2 + 2), x)
```

```@example symbolicutils
integrate(exp(a * x) * sin(x), x)
```

## Symbolics.jl

Symbolics wraps its SymbolicUtils terms in `Num`, which does not implement the TermInterface
methods: unwrap the integrand and the variable, and wrap the answer again.

```julia
using Symbolics
using RischIntegrate: integrate
@variables x

∫(f, x) = Num(integrate(Symbolics.unwrap(f), Symbolics.unwrap(x)))
∫(1 / (x^2 + 2), x)       # (1//2)*atan((1//2)*sqrt(2)*x)*sqrt(2)
```

## Giac.jl

Giac terms implement the TermInterface methods (through Giac's TermInterface extension) and are
integrated directly; Giac's `ln` is read as `log`:

```julia
using Giac
using RischIntegrate: integrate
@giac_var x

integrate(log(x)^2, x)      # 2*x-2*x*ln(x)+x*ln(x)^2
integrate(1 / (x^2 + 2), x) # 1/2*sqrt(2)*atan(sqrt(2)/2*x)
```

## Expr and other term types

The keywords `build` and `lift` say how the answer is built: `build(op, args...)` makes the term
for the function `op` (`+`, `*`, `sqrt`, `log`, …) applied to the terms `args`, and `lift(n)`
turns a Julia number into a term. By default operations are called as functions. For `Expr`:

```@example expr
using RischIntegrate: integrate
build(op, args...) = Expr(:call, nameof(op), args...)

integrate(:(x * exp(x)), :x; build = build, lift = identity)
```

## Non-elementary integrals

Integrals that can be written with the special functions of
[SpecialFunctions.jl](https://github.com/JuliaMath/SpecialFunctions.jl) (`expinti`, `sinint`,
`cosint`, `erf`, `erfi`) and [PolyLog.jl](https://github.com/Expander/PolyLog.jl) (`li2`) are
returned that way, when the term type has methods for them (SymbolicUtils does):

```@example symbolicutils
integrate(exp(-x^2), x)
```

```@example symbolicutils
integrate(sin(x) / x, x)
```

```@example symbolicutils
integrate(log(x) / (1 + x), x)
```

If the term type has no method for the special function (e.g. `sinint(x)` for a symbolic `x`),
the call raises its `MethodError`. [`NotElementary`](@ref RischIntegrate.NotElementary) is thrown
when the integral is proved to be non-elementary and has no such form:

```@example symbolicutils
try
    integrate(exp(x) / log(x)^2, x)
catch e
    sprint(showerror, e)
end
```

and [`RischNotImplemented`](@ref RischIntegrate.RischNotImplemented) when the integrand lies outside the cases implemented, for
example square roots of polynomials of degree greater than 2, which need the algebraic case of
the Risch algorithm:

```@example symbolicutils
try
    integrate(sqrt(x^3 + 1), x)
catch e
    sprint(showerror, e)
end
```

## RootSums

When the residues of the logarithmic part are algebraic of degree greater than 2, the answer is
an [`IntegralWithRootSums`](@ref RischIntegrate.IntegralWithRootSums): an elementary term plus sums over the roots of a polynomial.
It can be evaluated numerically; the logarithms are continued along the real line, so
`F(b) - F(a)` is a definite integral:

```@example symengine
F = integrate(1 / (x^5 + x + 1), x)
```

```@example symengine
F(2.0) - F(1.0)
```
