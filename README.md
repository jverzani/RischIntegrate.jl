# RischIntegrate

[![Dev](https://img.shields.io/badge/docs-dev-blue.svg)](https://jverzani.github.io/RischIntegrate.jl/dev/)
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

See the [documentation](https://jverzani.github.io/RischIntegrate.jl/dev/) for SymbolicUtils.jl,
Symbolics.jl, SimpleExpressions.jl and `Expr`, non-elementary integrals and RootSums.

## Comparison

The 175 integrals of `test/test_apostol.jl` (from Apostol's *Calculus*, as collected by
SymbolicIntegration.jl), counting an integral as solved when `integrate` returns an answer:

| Term type                                 | Solved |
|:------------------------------------------|-------:|
| SimpleExpressions.jl 1.3.2                |    163 |
| SymbolicUtils.jl 4                        |    163 |
| SymEngine.jl 0.13                         |    150 |
| Giac.jl 0.14 terms                        |    140 |
| Giac's own `integrate` (for reference)    |    172 |

SymEngine terms have no methods for `expinti`, `sinint`, `cosint` or `li2`, so the integrals
whose answers need these functions fail with a `MethodError`. Giac terms also write `log` as
`ln`, which is not recognized. Most of the remaining integrals that RischIntegrate does not
solve have a symbolic parameter (such as `n` in ``x^n \log(a x)``) whose answer depends on
cases; Giac assumes generic values for the parameters.
