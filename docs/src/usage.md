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
# (SymJ shows its terms as typeset math itself, through its Latexify extension)
using Latexify, SymEngine, SymbolicUtils
for T in (SymEngine.Basic, SymbolicUtils.BasicSymbolic)
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

## SymJ.jl

[SymJ.jl](https://github.com/jverzani/SymJ.jl) loads an extension with RischIntegrate. Its
`integrate` method adds piecewise functions (`abs`, `sign`, `heaviside`), assumptions on the
parameters (`assume = …`), and definite integrals split at the integrand's singular points:

```@example symj
using SymJ
using RischIntegrate: integrate
@syms x

integrate(log(x)^2, x)
```

```@example symj
integrate(1 / (x * sqrt(x^2 + 1)), x)
```

```@example symj
integrate((5 - sin(x)) * sqrt(sin(x)^2 + cos(x)^2), (x, 0, π))   # mass of a half circle
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

The macro [`@integrate`](@ref) does this without quoting, so no symbolic package is needed
(`$v` puts in the value of a variable `v`):

```@example expr
using RischIntegrate
@integrate(x * exp(x), x)
```

```@example expr
@integrate(sin(x), (x, 0, π))
```

The bounds of a definite integral are evaluated, so a bound in the variable of a later integral is
quoted. Over the region between y = x² and y = x for 0 ≤ x ≤ 1:

```@example expr
@integrate(x + y, (y, :(x^2), :x), (x, 0, 1))
```

## What an answer means

An answer `F` to `integrate(f, x)` satisfies `F′ = f` as functions of a real `x`, on each interval
where the integrand's radicals are real (their radicands positive) and that contains no pole of
`f` or `F`. Other symbols are parameters, and the answer holds **for every generic real value of
them**, not only for positive ones: ``∫ 1/(x^2 + a)`` is ``\operatorname{atan}(x/\sqrt a)/\sqrt a``,
correct for ``a < 0`` too, where ``\sqrt a`` is imaginary.

- A logarithm ``\log w`` of a negative ``w`` differs from ``\log|w|`` by the constant ``iπ``. Where
  a radical of a parameter is taken out, as in ``(c\,V)^e = c^e V^e``, the answer carries the factor
  ``(c\,V)^e/(c^e V^e)``, which is ``1`` for ``c > 0`` and constant on each interval for any sign of ``c``.
- A sign is used only when it is known: a rational number, a constant such as ``π``, or the
  caller's sign oracle (the `sign` keyword, step SO), which can give simpler real forms.
- Special functions follow the same rule where a single form exists for every sign. ``Li_2`` answers
  hold on the interval next to the zero of the logarithm's argument, and ``{}_2F_1`` answers hold where
  the hypergeometric argument is below 1.

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
example a square root of a logarithm:

```@example symbolicutils
try
    integrate(sqrt(log(x)), x)
catch e
    sprint(showerror, e)
end
```

## Non-elementary algebraic integrals: ₂F₁

For a radical of a binomial `α + βxⁿ` (`α > 0`), the part of a non-elementary integral that is left after
the algebraic and logarithmic parts is written with Gauss's hypergeometric function
(`HypergeometricFunctions._₂F₁`), as Rubi does:
`∫ xᵐ(α + βxⁿ)^q dx = α^q x^(m+1)/(m+1) ₂F₁(-q, (m+1)/n; (m+1)/n + 1; -βxⁿ/α)`. The answer is an
`IntegralWithRootSums` (the ₂F₁ terms are evaluated numerically):

```@example symengine
F = integrate(sqrt(x^3 + 1), x)
```

```@example symengine
F(2.0) - F(1.0)
```

Set `RischIntegrate.HYP_ANSWERS[] = false` to get [`NotElementary`](@ref RischIntegrate.NotElementary) instead.

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

An answer with parameters is evaluated with values for them, as pairs after the variable's (real values):

```@example symengine
@vars a b
G = integrate(1 / (x^4 + a * x + b), x)
G(x => 2.0, a => 1.0, b => 3.0) - G(x => 1.0, a => 1.0, b => 3.0)
```
