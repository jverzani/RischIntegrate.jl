# RischIntegrate.jl

Symbolic integration following Bronstein,
[*Symbolic Integration I: Transcendental Functions*](https://link.springer.com/book/10.1007/b138171),
for any symbolic term type that implements the
[TermInterface.jl](https://github.com/JuliaSymbolics/TermInterface.jl) methods `iscall`,
`operation` and `arguments`: [SymEngine.jl](https://github.com/symengine/SymEngine.jl),
[SymJ.jl](https://github.com/jverzani/SymJ.jl),
[SymbolicUtils.jl](https://github.com/JuliaSymbolics/SymbolicUtils.jl),
[Symbolics.jl](https://github.com/JuliaSymbolics/Symbolics.jl) (see [Usage](@ref)), [Giac.jl](https://github.com/JuliaGiac/Giac.jl), and Julia's `Expr`. All algebra is done with the package's own exact polynomial and rational-function types, and answers are rebuilt in the user's term type by calling operations as functions.

Every answer is checked by differentiation, exactly, before it is returned. When there is no
answer, the package says why: [`NotElementary`](@ref RischIntegrate.NotElementary) when the integral is proved to have no
elementary antiderivative, [`RischNotImplemented`](@ref RischIntegrate.RischNotImplemented) when the integrand lies outside the cases
implemented.

This package was implemented by Claude Code. The repository
[SymbolicIntegration.jl](https://github.com/JuliaSymbolics/SymbolicIntegration.jl) was not
consulted; it too implements the algorithm, but is coupled with Symbolics. The goal here was to
relax that dependence.

## Example

```@example index
using SymEngine: @vars
using RischIntegrate: integrate
@vars x

integrate(exp(x) / (exp(x) + 1)^2, x)     # indefinite
```

```@example index
integrate(sin(x), (x, 0, pi))             # definite
```

```@example index
integrate(1 / (x^3 + 1), x)
```

The entry points are [`integrate`](@ref), for the terms of a symbolic package, and the macro
[`@integrate`](@ref), for Julia expressions.

## Without a symbolic package: `@integrate`

[`@integrate`](@ref) takes the integrand as Julia code, unquoted, and the answer is a plain
Julia **`Expr`**, not a term of a symbolic package:

```@example macro
using RischIntegrate
F = @integrate(x * exp(x), x)
```

```@example macro
typeof(F)
```

Being an `Expr`, the answer can be evaluated, or turned into a function:

```@example macro
f = eval(:(x -> $F))
f(2.0)                       # (2 - 1)·e²
```
