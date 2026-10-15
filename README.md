# RischIntegrate

[![Build Status](https://github.com/jverzani/RischIntegrate.jl/actions/workflows/CI.yml/badge.svg?branch=main)](https://github.com/jverzani/RischIntegrate.jl/actions/workflows/CI.yml?query=branch%3Amain)


This is

> Symbolic integration following Bronstein, [*Symbolic Integration I: Transcendental Functions*](https://books.google.com.sg/books?id=pwQyR3hayFMC&printsec=copyright#v=onepage&q&f=false), for any symbolic term type that implements the TermInterface.jl methods `iscall`, `operation` and `arguments` (SimpleExpressions.jl, SymEngine.jl, `Expr`, ...). Only very light dependencies are required: all algebra is done by this module's own exact, dependency-free polynomial / rational-function types, and results are rebuilt by calling operations as functions.

This was completely implemented by Claude Code, which presumably had "read" the book.

The repository https://github.com/JuliaSymbolics/SymbolicIntegration.jl was not consulted. It too has an implementation of the algorithm, but is loosely coupled with Symbolics. The goal here was to relax that dependence.

The only entry point is `RischIntegrate.integrate`.

## Example

```{julia}
using SymEngine: @vars
using RischIntegrate: integrate
@vars x
integrate(exp(x) / (exp(x) + 1)^2, x) # indefinite, -1/(1 + exp(x))
integrate(sin(x), (x, 0, pi))         # definite, 2
```

## Using SymbolicUtils.jl and Symbolics.jl

SymbolicUtils terms implement the TermInterface methods, so they can be integrated directly.
Constants such as `sqrt(2)` are kept exact (built with `TermInterface.maketerm`, as SymbolicUtils
would otherwise evaluate `sqrt(2)` to a floating point number):

```{julia}
using SymbolicUtils: @syms
using RischIntegrate: RischIntegrate, integrate
@syms x::Real

integrate(1 / (x^2 + 2), x)        # (1//2)*atan((1//2)*sqrt(2)*x)*sqrt(2)
integrate(exp(-x^2), x)            # (1//2)*SpecialFunctions.erf(x)*sqrt(π)
integrate(log(x) / (1 + x), x)     # PolyLog.li2(1 / (1 + x)) + (1//2)*(log(1 + x)^2)
```

Symbolics.jl wraps its SymbolicUtils terms in `Num`, which does not implement the TermInterface
methods: unwrap the integrand and the variable, and wrap the answer again:

```{julia}
using Symbolics
using RischIntegrate: RischIntegrate, integrate
@variables x

∫(f, x) = Num(integrate(Symbolics.unwrap(f), Symbolics.unwrap(x)))
∫(1 / (x^2 + 2), x)                # (1//2)*atan((1//2)*sqrt(2)*x)*sqrt(2)
```

An answer that contains a `RootSum` (residues of degree greater than 2, for example
`1 / (x^3 + 2)`) is a `RischIntegrate.IntegralWithRootSums`, which is not a SymbolicUtils term (and
can not be wrapped in `Num`):

```{julia}
F = integrate(Symbolics.unwrap(1 / (x^3 + 2)), Symbolics.unwrap(x))
F isa RischIntegrate.IntegralWithRootSums   # true
```

The keywords `build` and `lift` of `integrate` control how answers are built for other term types;
see the docstring.
