# RischIntegrate

[![Dev](https://img.shields.io/badge/docs-dev-blue.svg)](https://jverzani.github.io/RischIntegrate.jl/dev/)
[![Build Status](https://github.com/jverzani/RischIntegrate.jl/actions/workflows/CI.yml/badge.svg?branch=main)](https://github.com/jverzani/RischIntegrate.jl/actions/workflows/CI.yml?query=branch%3Amain)
[![Apostol, verified of 175: RischIntegrate 161, SymbolicIntegration Risch 97](https://img.shields.io/badge/apostol%2C%20verified%20of%20175-RischIntegrate%20161%20%C2%B7%20SymbolicIntegration%20Risch%2097-2f8a4c)](https://rawcdn.githack.com/jverzani/RischIntegrate.jl/893583d2c85bc42167b37090e6c663539f1bce8f/benchmark/apostol/results/apostol_comparison.html)


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

The apostol badge compares RischIntegrate, with SymbolicUtils terms, to the Risch method of
SymbolicIntegration.jl, with Symbolics terms: the number of the 175 problems of
`test/test_apostol.jl` (from Apostol's *Calculus*, as collected by SymbolicIntegration.jl) each
integrates with an answer that checks out numerically. The [comparison](https://htmlpreview.github.io/?https://github.com/jverzani/RischIntegrate.jl/blob/main/benchmark/apostol/results/apostol_comparison.html) also has
RischIntegrate with SymEngine, `Expr`, SimpleExpressions and Giac.jl terms, and Giac's own
`integrate` for reference; see `benchmark/apostol/README.md` to rerun it.
