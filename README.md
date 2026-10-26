# RischIntegrate

[![Dev](https://img.shields.io/badge/docs-dev-blue.svg)](https://jverzani.github.io/RischIntegrate.jl/dev/)
[![Build Status](https://github.com/jverzani/RischIntegrate.jl/actions/workflows/CI.yml/badge.svg?branch=main)](https://github.com/jverzani/RischIntegrate.jl/actions/workflows/CI.yml?query=branch%3Amain)
[![Apostol, verified of 175: RischIntegrate 174, SymbolicIntegration Risch 97](https://img.shields.io/badge/apostol%2C%20verified%20of%20175-RischIntegrate%20174%20%C2%B7%20SymbolicIntegration%20Risch%2097-2f8a4c)](https://rawcdn.githack.com/jverzani/RischIntegrate.jl/bed5aa02a6d98a833ac6bcbfd986f3ab3c104b01/benchmark/apostol/results/apostol_comparison.html)


A package for symbolic integration in Julia, for any symbolic term type that implements the `TermInterface.jl` methods `iscall`, `operation` and `arguments` (`SymbolicUtils.jl`, `SymEngine.jl`, `Expr`, ...). Only very light dependencies are required; all algebra is done by this module's own exact, dependency-free polynomial / rational-function types, and results are rebuilt by calling operations as functions.

This work follows Bronstein, [*Symbolic Integration I: Transcendental Functions*](https://books.google.com.sg/books?id=pwQyR3hayFMC&printsec=copyright#v=onepage&q&f=false). Bronstein's book covers the transcendental case, but this package also integrates many algebraic integrands (radicals of rational functions, including hyperelliptic and Kummer cases, nested radicals, radicals of exponential and trigonometric functions and radicands with symbolic parameters), along the lines Bronstein's unwritten *Symbolic Integration II* would have taken (see `SI2_PLAN.md`). The package also gives non-elementary answers with special functions where they are standard (Ei, Si, Ci, Shi, Chi, erf, Li₂, Γ, ₁F₁, ₂F₁).

This was implemented by Claude Code, which presumably had "read" the book and then some.


## Example

The entry points are `integrate`, for the terms of a symbolic package, and the macro `@integrate`, for CAS-independent integration.


```{julia}
using SymEngine: @vars
using RischIntegrate: integrate
@vars x
integrate(exp(x) / (exp(x) + 1)^2, x) # indefinite, -1/(1 + exp(x))
integrate(sin(x), (x, 0, pi))         # definite, 2
```


The macro `@integrate` integrates Julia expressions; other names are parameters, and `$v` puts in the value of a variable `v`:

```{julia}
using RischIntegrate
@integrate(x * exp(x), x)         # (-1 + x) * exp(x)
@integrate(sin(x), (x, 0, π))     # 2.0
@integrate(a * x^2, (x, 0, 1))    # an expression in the parameter a
```

This is possible, as `Expr` objects support `TermInterface.jl`.
The bounds are evaluated as Julia values, so in an iterated integral over a region that is not a
rectangle, a bound in the variable of an outer integral must be quoted. Over the triangle
0 ≤ x ≤ y ≤ 1, the inner bound is `:y`:

```{julia}
@integrate(x * y, (x, 0, :y), (y, 0, 1))              # 0.125
```

## Comparisons

The Apostol badge links to a report comparing coverage and performance on 175 problems from Apostol's *Calculus*, as collected by [`SymbolicIntegration.jl`](https://github.com/JuliaSymbolics/SymbolicIntegration.jl): this package with different symbolic systems in Julia, the `RischMethod` of `SymbolicIntegration.jl`, and Giac's own implementation of integration. Giac is faster; `RischIntegrate.jl` has slightly better coverage.

On a wider set of 1680 sample problems from the same collection (the test suite of Rubi), the results are:

| System | Verified¹ (of 1680) | Unevaluated | Timed out | Total time | Median time (verified) |
|:---|---:|---:|---:|---:|---:|
| `RischIntegrate.jl` (`Expr` terms) | 1662 (98.9%) | 16 | 0 | 3.3 min | < 0.005 s |
| Giac 2.0.0 (`Giac.jl` 0.14.3) | 1534 (91.3%) | 127 | 0 | 0.3 min | < 0.005 s |
| SymPy 1.14.0 (`SymPyPythonCall.jl` 0.5.1) | 1333 (79.3%) | 251 | 63 | 84 min | 0.03 s |


¹ Answers may contain special functions, as Rubi's do. An answer counts as verified when its derivative matches the integrand numerically at two points (parameters set to fixed positive values). An answer that only fails there because it is written for the real line (`ln|u|`, `sign(u)`) and the points are outside its domain was checked again at two real points of the domain. For SymPy, parameters were declared positive, to match the assumptions of this package.
