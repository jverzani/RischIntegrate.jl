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
