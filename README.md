# RischIntegrate

[![Dev](https://img.shields.io/badge/docs-dev-blue.svg)](https://jverzani.github.io/RischIntegrate.jl/dev/)
[![Build Status](https://github.com/jverzani/RischIntegrate.jl/actions/workflows/CI.yml/badge.svg?branch=main)](https://github.com/jverzani/RischIntegrate.jl/actions/workflows/CI.yml?query=branch%3Amain)
[![Apostol, verified of 175: RischIntegrate 174, SymbolicIntegration Risch 97](https://img.shields.io/badge/apostol%2C%20verified%20of%20175-RischIntegrate%20174%20%C2%B7%20SymbolicIntegration%20Risch%2097-2f8a4c)](https://rawcdn.githack.com/jverzani/RischIntegrate.jl/bed5aa02a6d98a833ac6bcbfd986f3ab3c104b01/benchmark/apostol/results/apostol_comparison.html)


This is

> Symbolic integration following Bronstein, [*Symbolic Integration I: Transcendental Functions*](https://books.google.com.sg/books?id=pwQyR3hayFMC&printsec=copyright#v=onepage&q&f=false) with extensions to algebraic functions, for any symbolic term type that implements the TermInterface.jl methods `iscall`, `operation` and `arguments` (SymbolicUtils.jl, SymEngine.jl, `Expr`, ...). Only very light dependencies are required: all algebra is done by this module's own exact, dependency-free polynomial / rational-function types, and results are rebuilt by calling operations as functions.

This was implemented by Claude Code, which presumably had "read" the book and then some.

`Symbolics.jl` has the package [SymbolicIntegration.jl](https://github.com/JuliaSymbolics/SymbolicIntegration.jl) supporting symbolic integration. The code base was not specifically consulted here, but its compilation of 1680 sample integration problems was extremely useful in the development of this package.



Bronstein's book covers the transcendental case, but this package also integrates many algebraic integrands (radicals of rational functions, including hyperelliptic and Kummer cases, nested radicals, radicals of exponential and trigonometric functions and radicands with symbolic parameters), along the lines Bronstein's unwritten *Symbolic Integration II* would have taken (see `SI2_PLAN.md`). The package also gives non-elementary answers with special functions where they are standard (Ei, Si, Ci, Shi, Chi, erf, Li₂, Γ, ₁F₁, ₂F₁).

The entry points are `integrate`, for the terms of a symbolic package, and the macro `@integrate`, for CAS-independent integration.

## Example

```{julia}
using SymEngine: @vars
using RischIntegrate: integrate
@vars x
integrate(exp(x) / (exp(x) + 1)^2, x) # indefinite, -1/(1 + exp(x))
integrate(sin(x), (x, 0, pi))         # definite, 2
```

As `Expr` objects support `TermInterface`, we can integrate without a symbolic package. The macro `@integrate` integrates Julia expressions; other names are parameters, and `$v` puts in the value of a variable `v`:

```{julia}
using RischIntegrate
@integrate(x * exp(x), x)         # (-1 + x) * exp(x)
@integrate(sin(x), (x, 0, π))     # 2.0
@integrate(a * x^2, (x, 0, 1))    # an expression in the parameter a
```

The bounds are evaluated as Julia values, so in an iterated integral over a region that is not a
rectangle, a bound in the variable of an outer integral must be quoted. Over the triangle
0 ≤ x ≤ y ≤ 1, the inner bound is `:y`:

```{julia}
@integrate(x * y, (x, 0, :y), (y, 0, 1))              # 0.125
@integrate(x + y, (y, :(x^2), :x), (x, 0, 1))         # between y = x² and y = x
@integrate(x * y, (x, 0, y), (y, 0, 1))               # UndefVarError: y is evaluated, not quoted
```

## Comparison

The apostol badge compares RischIntegrate, with SymbolicUtils terms, to the Risch method of
SymbolicIntegration.jl, with Symbolics terms: the number of the 175 problems of
`test/test_apostol.jl` (from Apostol's *Calculus*, as collected by SymbolicIntegration.jl) each
integrates with an answer that checks out numerically. The [comparison](https://rawcdn.githack.com/jverzani/RischIntegrate.jl/bed5aa02a6d98a833ac6bcbfd986f3ab3c104b01/benchmark/apostol/results/apostol_comparison.html) also has
RischIntegrate with SymEngine, `Expr`, SimpleExpressions and Giac.jl terms, and Giac's own
`integrate`.

The 1680 sample problems compiled by SymbolicIntegration.jl (from the test suite of Rubi) give a wider comparison. Each system integrates every problem, with a limit of 60 s per problem, and an answer counts as verified when its derivative matches the integrand numerically at two points (parameters set to fixed positive values). An answer that only fails there because it is written for the real line (ln|u|, sign(u)) and the points are outside its domain was checked again at two real points of the domain. Answers may contain special functions, as Rubi's do.

| System | Verified (of 1680) | Unevaluated | Timed out | Total time | Median time (verified) |
|:---|---:|---:|---:|---:|---:|
| RischIntegrate (`Expr` terms) | 1641 (97.7%) | 33 | 0 | 3.6 min | < 0.005 s |
| Giac 2.0.0 (Giac.jl 0.14.3) | 1534 (91.3%) | 127 | 0 | 0.3 min | < 0.005 s |
| SymPy 1.14.0 (SymPyPythonCall 0.5.1) | 1333 (79.3%) | 251 | 63 | 84 min | 0.03 s |

Notes:

- "Unevaluated" counts refusals: `NotElementary` or `RischNotImplemented` for RischIntegrate (4 of its 33 are problems Rubi itself leaves unintegrated), an unevaluated integral for Giac and SymPy.
- RischIntegrate's 6 others are 5 answers that the check misjudges by floating-point cancellation (they verify in `BigFloat` arithmetic) and 1 answer with a `RootSum` over a symbolic parameter, which cannot be evaluated numerically. Giac's 19 others are 9 answers that still fail the check and 10 whose integrand is real at none of the points tried. SymPy's 33 others are 24 wrong answers (∫ 1/(a x² + b x + c) = 0, ∫ 1/(x⁶ - 2) with only the real logarithms, ...), 5 with no real points, and 4 errors.
- SymPy's parameters were declared positive. Times are wall-clock on an Apple M4, run in one process per system (compilation included); for Giac and SymPy they include the numerical check.
