# Design notes

RischIntegrate.jl finds antiderivatives of expressions built by other symbolic packages. The core
is the transcendental Risch algorithm as presented in Bronstein's *Symbolic Integration I*. Around
it is a sequence of substitutions, rewrites and special-function steps that bring other integrands
to the cases the algorithm handles. This page describes how the pieces fit together and follows an
integrand through the steps that look for its antiderivative.

The source refers to its steps by short codes (step EP, step US, step RC, …). The codes are used
here too, so a passage of these notes can be matched with the comment in `src/` that implements it.
A table of all of them is at the end.

## Goals

- **Any term type.** The input is any term that implements the
  [TermInterface.jl](https://github.com/JuliaSymbolics/TermInterface.jl) methods `iscall`,
  `operation` and `arguments`: SymEngine, SymbolicUtils, Symbolics, SimpleExpressions, Giac, or
  Julia's `Expr`. The package reads the term, but does no arithmetic with it.
- **Exact algebra of its own.** Every computation is done with the package's own dense polynomials
  and rational functions over exact fields: ``ℚ``, ``ℚ(i)``, quadratic fields, and rational
  function fields of parameters and transcendental constants. No other CAS is called.
- **Answers in the user's term type.** The result is rebuilt by calling operations as functions
  (`+`, `*`, `log`, `atan`, …) on the user's terms. The keywords `build` and `lift` change how
  that happens.
- **Verified answers.** Every answer is differentiated and compared with the integrand, exactly, in
  the field where it was computed. A failed check is a `RischError`, that is, a bug.
- **Honest refusals.** Without an answer, the package says why: `NotElementary` when the integral
  is proved to have no elementary antiderivative (and no form with the special functions used
  here was found), `RischNotImplemented` when the integrand is outside the implemented cases.
- **Real answers on the real line.** For a real integrand, the answer is a real expression,
  continuous where the integrand is, whenever the algorithm can arrange it (real forms of complex
  logarithms, `atan`s of polynomials instead of rational functions, jump corrections for
  `tan`-substitutions).

Simplifying expressions in symbolic constants, such as ``\cos^2 a + \sin^2 a = 1``, is left to the
caller's CAS.

## Architecture

An integral goes through three layers:

```
 user's term ──parse──▶ element of an exact differential field ──integrate──▶ exact answer
                        (tower ℚ(x)(θ₁)…(θₙ) over a constant field)          (verified there)
                                                                                    │
 user's term ◀──────────────────────────── build ───────────────────────────────────┘
```

1. **Parse.** The term is read into an element of a differential field: a rational function in
   `x` over a constant field, or a *tower* ``K_n = ℚ(x)(θ_1)…(θ_n)`` of transcendental monomials
   (`exp`, `log`, `atan`). Symbols other than `x` become indeterminates of the constant field.
2. **Integrate.** The Risch algorithm runs on that element. Its result (a rational part, sums of
   logarithms and arctangents, RootSums, special-function terms) is checked by differentiation in
   the same field.
3. **Build.** The result is written out as a term of the user's package.

Most integrands do not parse directly: radicals, `asin`, compositions such as ``f(x + 1/x)``.
For those, a step rewrites or substitutes until the pieces do parse, integrates, and maps the
answer back. The chain rule check that comes with each substitution keeps the result verified.

### Source layout

`src/RischIntegrate.jl` includes the files in dependency order. Grouped by layer:

| Layer | Files |
|:------|:------|
| exact algebra | `core.jl`, `polynomials.jl`, `fractions.jl`, `factoring.jl`, `number_fields.jl`, `constant_fields.jl`, `sturm.jl` |
| rational functions | `hermite_reduction.jl`, `rothstein_trager.jl`, `log_to_atan.jl`, `quartic_residues.jl`, `rootsum.jl` |
| terms ↔ fields | `term_input.jl`, `term_output.jl`, `tower_terms.jl`, `rootsum_numerics.jl` |
| towers | `tower.jl`, `structure_theorems.jl`, `monomial_integration.jl`, `rde_base.jl`, `risch_de.jl`, `parametric_rde.jl`, `tower_rootsums.jl`, `tower_real_forms.jl`, `real_form.jl` |
| special functions | `special_functions.jl`, `dilogarithms.jl`, `exp_trig_polynomials.jl`, `clausen.jl`, `polylog_parts.jl`, `hypergeometric.jl`, `hyp_symbolic.jl`, `exp_trig_hyp.jl`, `gamma_terms.jl`, `special_fallback.jl` |
| algebraic integrands | `radicals.jl`, `euler_substitutions.jl`, `biquadratic.jl`, `hyperelliptic.jl`, `kummer.jl`, `kummer_logs.jl`, `param_radicals.jl`, `denest.jl`, `nested.jl`, `nested_subst.jl`, `constant_scaling.jl`, `monomial_radicals.jl`, `reciprocal_subst.jl`, `tower_radicals.jl`, `real_log_arguments.jl` |
| substitutions and rewrites | `bioche.jl`, `inverse_trig.jl`, `u_substitution.jl`, `linearity.jl` |
| entry points | `risch_integrate.jl`, `integrate_macro.jl`, `precompile.jl` |

## Exact algebra

### Polynomials and fractions

`UPoly{T}` is a dense univariate polynomial over a field `T`, coefficients from low to high
degree. It has Euclidean division, gcd and extended gcd, squarefree factorization, resultants and
the derivative. `Frac{P}` is the fraction field of a polynomial ring, kept normalized: numerator
and denominator coprime, denominator monic. The normal form is unique, so equality is structural.

Factoring over ``ℚ`` (`factoring.jl`) uses rational roots and Cantor–Zassenhaus. The logarithmic
part uses it on the residue polynomial over ``ℚ`` to find quadratic and quartic factors; RootSums
use dynamic evaluation instead, so the factors left for them need not be irreducible.

### Constant fields

The constants of the differential field form a type `C`:

| `C` | field | when |
|:----|:------|:-----|
| `Q` | ``ℚ`` | the default |
| `QI` | ``ℚ(i)`` | trigonometric input (Step 7) |
| `QS{d}`, `QSB{d,B}` | ``ℚ(\sqrt d)``, ``B(\sqrt d)`` with ``B = ℚ`` or ``ℚ(i)`` | quadratic residues, square roots of rational constants (step 10e), Euler substitutions without a rational point |
| `Frac{UPoly{B}}`, nested | ``ℚ(t_1, …, t_k)`` or ``ℚ(i)(t_1, …, t_k)`` | parameters and transcendental constants |

Each generator ``t_j`` of a rational function field is described by a `ConstGen`:

- `:sym`: a symbolic parameter, any symbol other than the variable (step SY). It is printed back as
  the user's own symbol.
- `:exp`: ``e^{1/s}``; at most one, so that ``e`` and its rational powers share a generator.
- `:log`: ``\log p`` for a prime ``p``; ``\log r = \sum v_p(r) \log p`` for ``r ∈ ℚ_+``.
- `:symlog`: ``\log a`` for a parameter ``a``.
- `:expi`: ``e^{i/s}`` over ``ℚ(i)``, for constants ``e^{iq}`` with ``q ∈ ℚ``; conjugation sends it to
  its inverse.

The generators are treated as algebraically independent. That is exact for one of ``e`` or
``\log 2``; for several together it is Schanuel's conjecture, which every CAS assumes. A computation
that meets a constant needing a new generator throws `NewConstants` with the longer list, and the
tower is built again over the larger field. Parameters nest the field one level deeper each, so
their number is capped (`MAX_PARAMS`).

Some decisions depend on the sign of a parameter expression: choosing `atan` or `log`, the sign of
a radicand, which branch of a square root. They are made at fixed values, the `k`-th parameter in
alphabetical order taking the value `k` (`param_value`). Answers therefore hold for the parameter
values that share those signs, the usual convention of symbolic integrators ("assume `a > 0`").

`sturm.jl` counts real roots and decides signs exactly with Sturm sequences, for ``ℚ`` and the real
quadratic fields, and numerically to 256 bits for parameter fields.

## Towers

A `Tower{C}` holds the levels ``θ_1, …, θ_n`` over ``K_0 = C(x)``. Level ``i`` is a `Level` with a
kind and an argument ``u ∈ K_{i-1}``:

| kind | monomial | derivation |
|:-----|:---------|:-----------|
| `:exp` | ``θ = e^u`` | ``θ' = u' θ`` |
| `:log` | ``θ = \log u`` | ``θ' = u'/u`` |
| `:atan` | ``θ = \operatorname{atan} u`` | ``θ' = u'/(1 + u^2)`` (step TA) |

The field ``K_i`` is the type `Frac{UPoly{K_{i-1}}}`, so the level of an element is part of its
type, and arithmetic between levels lifts the lower operand (`liftto`, `unify`).

A new monomial is added only when it is algebraically independent of the levels below; otherwise it
is written in terms of them. The structure theorems (Risch; Bronstein ch. 9) decide this by exact
linear algebra over ``ℚ``: ``e^u`` is not new when ``u' = \sum ρ_i b_i'`` with ``ρ_i ∈ ℚ`` (``b_i``
the arguments of `exp` levels and the `log` monomials), and then
``e^u = e^c \prod θ_i^{ρ_i} \prod \arg_i^{ρ_i}``. So ``e^{2x}`` is ``θ^2`` over ``θ = e^x``,
``e^{\log x} = x``, and ``\log(x^2 - 1) = \log(x - 1) + \log(x + 1)``. When ``e^{x/2}`` appears after
``e^x``, the generator is refined to ``e^{x/2}`` (a `Restart`) and the term is parsed again.

### Parsing a term

`build_tower(f, x)` calls `parse_tower` and retries on three signals:

- `Restart`: a finer exponential generator is needed (``e^{x/2}`` after ``e^x``);
- `NewConstants`: a new constant generator;
- `NeedComplex`: a trigonometric function appeared, so the constant field becomes ``ℚ(i)``.

`parse_tower` maps operations to field operations:

- `+`, `-`, `*`, `/`, integer powers: field arithmetic.
- `exp`, `ℯ^u`, `log`: new levels, through the structure theorems.
- `sin`, `cos`, `tan`, `cot`, `sec`, `csc` of ``u``: over ``ℚ(i)``, with ``E = e^{iu}``,
  ``\sin u = (E - E^{-1})/(2i)``, ``\cos u = (E + E^{-1})/2``, and so on (Step 7).
- `sinh`, `cosh`, …: through ``e^u`` and ``e^{-u}``.
- `atan`: an `:atan` level (step TA).
- ``u^k`` with a non-rational constant exponent ``k`` (a parameter, ``e``): ``e^{k \log u}``.
- Symbols other than `x`: parameters (step SY). A leaf that prints with `x` in it but does not open
  as a call (a wrapper type) is refused rather than read as a parameter (step WR).
- Radicals and other functions: `RischNotImplemented`. The steps of the next sections deal with
  them before the tower is built.

Two mechanisms let the later steps reuse `parse_tower`:

- **Parse hooks.** `T.subst(t, T)` is consulted first for every subterm. A substitution step sets it
  to map `x` to ``φ(t)`` and each radical to a power of ``t``, so the integrand is parsed directly
  in the new variable.
- **Opaque constants** (step SY). Any subterm can be made a `:sym` constant with `sym_const`.
  Radicals of parameters (``\sqrt{2h}``), trigonometric functions of parameters (``\cos a``), and
  square roots of negative constants (``\sqrt{-1}`` for ``i``) are opaque by default. Steps such as
  u-substitution use the same device to test whether an expression is a function of a chosen
  subterm. This is sound because the opaque constants are formally independent: an identity that
  holds for an indeterminate still holds after the actual subterm is put back.

## Following an integrand

`integrate(f, x)` calls `risch_integrate(f, x)`. Iterated integrals call it once per variable,
definite integrals evaluate the antiderivative at the limits.

`risch_integrate` has two parts. `integrate_direct` sends the integrand to the method that fits
its shape, and returns its answer or rethrows its refusal. When that refusal comes back, a
*fallback chain* tries methods that recognize a special structure. Both are described in order
below. Each step either returns a verified answer, returns `nothing` ("not my case", go on), or
throws. A step that rewrites the integrand calls `risch_integrate` again on the new form.

### 1. Rewrites before parsing (`integrate_direct`)

| Step | Recognizes | Does |
|:-----|:-----------|:-----|
| EP | ``(b^w)^r`` with a positive constant ``b``; ``(C^s)^n`` with integer ``n`` over products and quotients | merges exponents: ``(3^{3x})^{1/4} = 3^{3x/4}``, so a radicand with even powers of a radical becomes rational |
| erf | ``\int \operatorname{erf}(ax + b)`` | by parts |
| IT | a factor free of `x` that contains a symbol or a root ``c^{p/q}`` with ``q > 2`` | takes it out: ``\int c\,g = c \int g``. This keeps the parameter out of the constant field, and lets an iterated integral see ``c(y) \cdot \text{RootSum}(x)`` |
| TS2 | ``\sin(v + a)``, ``\cosh(v + a)``, … with ``a`` free of `x` | addition formulas, so ``\cos a``, ``\sin a`` become opaque constants. Exact values for multiples of ``π/6`` and ``π/4`` |
| AC | `acot`, `acsc`, `asec` | ``\operatorname{acot} u = \operatorname{atan}(1/u)``, ``\operatorname{acsc} u = \operatorname{asin}(1/u)``, … |
| AS | `asin(u)` or `acos(u)` with ``u`` linear | ``u = \sin t``: the integrand is rebuilt in ``t`` (`x` stands for ``t``), integrated, and mapped back, ``\sin kt``, ``\cos kt`` written exactly as ``A(u) + B(u)\sqrt{1 - u^2}`` |
| PL | no radicals, parameters, denominator a power of one quadratic | linearity over a parameter field |

### 2. Radicals

`collect_radicals` finds every ``u^{p/q}`` (`sqrt`, `cbrt`, `^` with a non-integer
rational exponent). Radicals of parameters are opaque constants and are not counted. Then:

| Step | Recognizes | Does |
|:-----|:-----------|:-----|
| AS | only powers of ``\sqrt{1 - u^2}``, ``u`` linear | ``u = \sin t`` first, which gives `asin(u)` instead of logarithms |
| PR (rational) | one quadratic radicand ``K - \lvert α \rvert (x - h)^2`` whose scaling to ``K(1 - u^2)`` is irrational, e.g. ``7 - 2x^2`` | step PR with the constant radicals opaque, so that the `asin` route applies in ``u`` |
| PR | parameters in a radicand: ``a^2 - x^2``, ``(x - a)(b - x)``, ``(a + x)/(a - x)`` | an affine ``x = s u + h`` over the parameter field makes the radicand ``κ R(u)`` with ``R`` free of parameters |
| NR | several radicands, one innermost radical of a linear radicand | ``u = \sqrt{\text{linear}}`` |
| MR | radicands that are functions of one ``e^{kx}``, ``\cos kx``, ``\sin kx`` or ``\tan kx`` (``\sqrt{1 + e^x}``) | substitute that function. The radicals are opaque constants while the identities ``g(s(θ))\,s' = R`` and ``\tilde U_j(s(θ)) = U_j`` are checked exactly. Before that, a cheap derivative-divides test with a radicand as ``u`` |
| PW | radicands that are perfect powers at a finer monomial | rewrite at ``e^{ckx/m}`` |
| DN | ``\sqrt{a + b\sqrt c}`` with ``a^2 - b^2 c`` a square | denest: ``\sqrt{p_1} + s\sqrt{p_2}`` |
| nested | ``\sqrt{a + b\sqrt c}`` with ``a^2 - b^2c = -s^2`` | a biquadratic field over ``ℚ(i)``, real parts taken exactly |

What is left goes to `integrate_radical`. Its cases, in order:

- **NP**: a square root of a radicand ``u ≤ 0`` on all of ``ℝ`` (checked exactly: no real root of
  odd multiplicity of ``N D``, ``\operatorname{lc}(ND) < 0``). On the principal branch
  ``u^{p/2} = i^p (-u)^{p/2}``, with ``i = \sqrt{-1}`` an opaque constant, and the rewritten
  integrand starts over.
- **10e**: square roots of rational constants (``\sqrt 2``, ``8^{3/2}``) become constants of
  ``ℚ(i)(\sqrt d)``; they must share one ``d``.
- **RP**: a radicand ``c\,w^m`` is read as a power of ``w``.
- **BQ**: two square roots, not both of linear polynomials: the biquadratic field
  ``ℚ(x)(\sqrt a, \sqrt b)`` splits into the three quadratic subfields by its Galois group, so
  ``\int f`` is elementary exactly when each projection is, and each is a one-radicand problem.
- **10d**: square roots of two linear polynomials: ``y = \sqrt{u_1}``, then an Euler substitution
  for ``\sqrt{u_2}`` (a conic).
- One radicand ``u``, index ``n``:
  - **SQ**: repeated factors, ``u = c\,S^2 W/(T^2 V)``: the variable is ``Y = \sqrt u/s``, with
    ``Y^2 = w`` on every interval, whatever the sign of ``s``. For ``n ≥ 3``, a radicand
    ``s^n (x - a)^j (x - b)^k`` reduces to a linear-fractional one.
  - **10a**: ``u = (ax + b)/(cx + d)``: ``t = u^{1/n}``, ``x = (b - d t^n)/(c t^n - a)``.
  - **10b/10c**: ``\sqrt{Ax^2 + Bx + C}``: an Euler substitution, a rational parametrization of the
    conic ``R^2 = Q`` over ``ℚ``, or over ``ℚ(i)(\sqrt d)`` when there is no small rational point.
    Several candidates are tried, one per constant field.
  - **hyperelliptic** (SI2 phase 1): ``\sqrt a`` with ``\deg a ≥ 3`` (genus ≥ 1). Hermite reduction
    on the curve, reduction at infinity; a residue-free remainder is zero or the integral is not
    elementary (Liouville).
- **Kummer** (SI2 phases 3a and 3b): products of radicals of any index, through the integral basis
  of the Kummer extension. The log part uses Riemann–Roch on the curve and yields a RootSum over
  the roots of unity. This runs when `integrate_radical` refuses.

A substitution step parses the integrand in the new variable ``t`` through a parse hook,
multiplies by ``φ'(t)``, integrates in the tower over ``ℚ(t)`` (or a larger constant field), and
verifies there. The answer is printed with ``t`` written as a term in `x`, so no substitution back
is needed at the term level. Steps RL and EL then make the arguments of logarithms real on the real
points of the substitution: ``\log(-w)`` for a negative ``w``, ``\log\lvert w \rvert`` for a ``w`` of
both signs.

Principal branches are used throughout: answers with ``u^{p/q}`` hold where ``u > 0``.

### 3. Trigonometric integrands

Two shortcuts before the general tower:

- **Stage 5c**: polynomials times ``e^{ax}`` times ``\sin``, ``\cos``, ``\sinh``, ``\cosh`` of linear
  arguments. In complex exponentials the integrand is ``\sum_λ P_λ(x) e^{λx}`` with ``λ ∈ ℚ(i)``,
  and ``\int P e^{λx} = e^{λx} \sum_k (-1)^k P^{(k)}/λ^{k+1}``. Conjugate pairs fold back to
  ``e^{ax}(A \cos bx + B \sin bx)``.
- **TS** (Bioche's rules): ``f`` rational in ``\sin u``, ``\cos u``. If ``f\,du`` is invariant under
  ``u ↦ -u``, ``π - u`` or ``π + u``, the substitution ``s = \cos u``, ``\sin u`` or ``\tan u``
  gives a rational integral in ``s``. The ``\tan`` substitution's answer jumps where ``\tan u = ±∞``;
  each ``c \operatorname{atan}(p)`` with ``p`` of odd degree gets the correction
  ``J π \lfloor (u + π/2)/π \rfloor``.

### 4. The tower

The general route: `build_tower`, then `integrate_built`, which calls `integrate_el(T, n, f)` on
the top level. A rational function (``n = 0``) is integrated directly:

1. **Hermite reduction** (Bronstein §2.2) gives the rational part and a remainder with a squarefree
   denominator.
2. **The logarithmic part.** The Rothstein–Trager resultant
   ``R(z) = \operatorname{res}_x(D, A - zD')`` is computed, and its roots in the constant field give
   ``c \log \gcd(D, A - cD')``. Over ``ℚ`` the factor that remains is factored. A quadratic factor,
   with residues ``a ± b\sqrt d``, gives logarithms over ``ℚ(\sqrt d)``, or `atan` terms for a
   complex pair. Rioboo's LogToAtan (§2.8) turns ``\operatorname{atan}(A/B)``,
   which jumps at the zeros of ``B``, into a sum of `atan`s of polynomials, continuous on the real
   line. Quartic residues are written with real radicals when their roots lie in one ``ℚ(i, \sqrt d)``
   (step R2). Step BQ4 handles an even quartic factor ``G = x^4 + bx^2 + c`` of the denominator
   with ``b^2 < 4c`` whose residues need nested radicals. Partial fractions split it off, and
   the factorization ``G = (x^2 + rx + q)(x^2 - rx + q)``, with ``q = \sqrt c`` and
   ``r = \sqrt{2q - b}``, gives continuous `atan`s and a `log` with nested constants, as in
   ``1/(x^8 + 4)``. Other residues of degree greater than 2 give a **RootSum**
   ``\sum_{Q(α) = 0} α \log W(α, x)``, with ``W`` computed by dynamic evaluation (`d5_gcd`), which
   splits ``Q`` when a leading coefficient turns out to be a zero divisor, so no factorization is
   needed.

A RootSum answer is not final. `risch_integrate` tries two rescalings ``x = ρu`` that move the
denominator to one over ``ℚ``, where the real forms above apply:

- **Step PS.** If ``f`` is homogeneous in ``x`` and a parameter ``a``, then ``ρ = a``.
  For example, ``1/(x^3 + a^3) = a^{-3}/(u^3 + 1)``.
- **Step BN.** If the denominator is ``λ x^j (x^n + c)^k`` with ``n ≥ 3``, then
  ``ρ = |c|^{1/n}``, kept as an opaque constant. For example, ``1/(x^3 - 2)`` and ``1/(a x^3 - b)``.
  Here ``x^n + c = |c|(u^n ± 1)``. The numerator is split into monomials ``u^i``, and powers of
  ``ρ`` are reduced with ``ρ^n = |c|``. That leaves one integral ``\int u^{i-j}/(u^n ± 1)^k`` over
  ``ℚ`` for each monomial. The factors of ``u^n ± 1`` are cyclotomic, so for ``n = 3, 4, 5, 6``
  the answer has only `log` and `atan`, with ``\sqrt 3``, ``\sqrt 2`` or ``\sqrt 5``.
  For ``u^8 + 1`` the integral stays a RootSum.
  If ``|c|`` is an ``n``-th power in the constant field, ``ρ`` is that root rather than an opaque
  constant: ``ρ = a`` for ``c = a^3``.

Either way the answer is ``G(x/ρ)``, which matches the ``b^{1/3}`` form Rubi gives.

Step BN is also tried inside the radical substitutions (`integrate_subst`), on the rational function
of ``t``. There ``t = x^{1/3}`` turns ``1/((a^3 - x) x^{4/3})`` into ``3/(t^2 (a^3 - t^3))``.
Together with step US (``u = \cos^n x``) this handles ``\tan x/(a^3 - b^3\cos^n x)^{4/3}``.

At a level ``i ≥ 1`` with monomial ``θ`` over ``K = K_{i-1}`` (Bronstein ch. 5):

1. **Special part** (exp only): ``θ^m`` in the denominator splits off as Laurent terms.
2. **Hermite reduction** with the tower derivation.
3. **Residue criterion** (Thm 5.6.1): ``R(z) = \operatorname{res}_θ(D, A - z\,δD)`` must have constant
   roots, or the integral is not elementary. The roots give ``\sum c \log \gcd(D, A - c\,δD)``. For
   exp levels ``\int v'/v`` carries an extra ``-\deg(v)\,u``. Non-rational residues give RootSums
   inside the tower (step RT), with real forms for quartics (step RF).
4. **Polynomial part.**
   - `log` and `atan` levels (primitive): top-down reduction, each coefficient by *limited
     integration* in ``K`` (§5.8), recursively calling `integrate_el` at level ``i - 1``. When
     that is impossible because of ``θ \log(ax + b)`` times simple rational poles, the dilogarithm
     step DL writes those terms with ``\operatorname{Li}_2``; step LF handles logs of products of
     linear factors. These include the roots of quadratics in one real ``ℚ(\sqrt d)``, for example
     ``\log(x^2 + x - 1) = \log(x - r_+) + \log(x - r_-)``. Poles of order ``j ≥ 2`` are moved by
     parts: ``θ\,c/(x - c_0)^j = (Eθ)' - Eθ'`` with ``E = -c/((j - 1)(x - c_0)^{j-1})``, and the
     rational term ``-Eθ'`` joins the coefficient of ``θ^0``.
     **Step DC** handles a quadratic factor ``Q = (x - α)^2 + β^2`` with complex roots
     ``c = α ± iβ`` and poles of the coefficient at those roots. Its integral is
     ``2\operatorname{Re}[γ(\tfrac12\log^2(x - c) + \log(x - \bar c)\log w + \operatorname{Li}_2(\bar w))]``
     with ``w = ½ + i(x - α)/(2β)``. Since ``\operatorname{Re} w = ½``, no `log` or ``\operatorname{Li}_2`` crosses a
     branch cut, and the real form (`atan`, `repolylog`, `impolylog`) is continuous on ``ℝ``. An example is
     ``\int \log(x^2 + 2)^2``. Each pair of complex poles ``c, \bar c`` contributes twice the real part of
     ``\int ρ \log v/(x - c)``. That real part uses ``\operatorname{Re}\operatorname{Li}_2`` and
     ``\operatorname{Im}\operatorname{Li}_2`` (`repolylog`, `impolylog`), and works over a
     parameter field too. The poles come from ``ℚ(i)``, or from a quadratic factor with
     ``-Δ`` a square, as in ``a ± i`` for ``1/(1 + (x - a)^2)``. That is how ``\int \operatorname{atan}(x - a)/(x + a)``
     is done, by parts (step AP).
   - `exp` levels: ``\int a_j θ^j`` needs ``y`` with ``y' + j u' y = a_j``, the **Risch differential
     equation** (ch. 6). `rde` dispatches: `rde_base` over ``C(x)`` (bounds on poles and degree,
     then exact linear algebra), and `rde_general` for arbitrary denominators (weak normalization,
     normal and special denominators, degree bound, SPDE, then the no-cancellation, decoupled or
     triangular cases). Cancellation cases (§6.6) are recognized but not solved: if one cannot be
     excluded and no solution is found, the answer is `RischNotImplemented`, not `NotElementary`.
5. **Special functions** (Step 8a). Where step 4 proves ``\int a θ^j`` (``θ = e^U``) not elementary,
   the parametric Risch equation (ch. 7, `prde`) looks for
   ``a = y' + jU'y + \sum c_t U'/(U - t) + \sum d_l θ_l^{-j} W_l'/W_l [+ k]``, which integrates with
   `Ei` terms, and `erf`/`erfi` for a quadratic exponent at the base. At a log level with
   non-constant residues, ``\int c\,u^m u'/(\log u + b)`` gives ``\operatorname{Ei}`` of a log
   (`li`). When the denominator has several factors, partial fractions first split off each factor
   ``θ - r`` with ``r`` constant (`special_log_split`). These factors are found as the common roots
   of the denominator and its coefficientwise derivative. Each such piece is integrated by the usual
   log part if possible (for example ``-\log\log x``), and otherwise as `Ei`. The rest goes to the
   usual log part. For example,
   ``\int (2θ^2 - θ - x^2)/(θ^3 - x^2 θ)`` with ``θ = \log x`` is
   ``\operatorname{Ei}(\log x) + \tfrac12\log(x + \log x) - \tfrac12\log(\log x - x)``.
   These terms keep their exact derivatives, so the usual check still applies.

Over ``ℚ(i)`` (trigonometric input) the integral is computed there and then put in **real form**
(Step 7). Conjugation ``σ`` (``i ↦ -i``, with ``σθ = θ`` for real generators and ``σθ = 1/θ`` for
``θ = e^{iw}``) commutes with the derivation, so ``\operatorname{Re} F = (F + σF)/2`` is also an
antiderivative. Its real form uses ``\cos kw``, ``\sin kw``, and
``(c \log w + σc \log σw)/2 = (c_r/2) \log(w\,σw) - c_i \operatorname{atan}(V/U)``, with
``c_r = (c + σc)/2``, ``c_i = (c - σc)/(2i)``, ``U = (w + σw)/2`` and ``V = (w - σw)/(2i)``. The real
form is verified again in the tower.

A `NotElementary` from a tower with an `atan` level is demoted to `RischNotImplemented`, since the
structure-theorem arguments behind some decisions are for `exp`/`log` towers only.

### 5. When the direct route fails: the fallback chain

If `integrate_direct` throws `NotElementary` or `RischNotImplemented`, `risch_integrate` tries, in
order:

| Step | When | Recognizes | Does |
|:-----|:-----|:-----------|:-----|
| CL | `NotElementary` | ``x^p R(\sin kx, \cos kx)`` | by parts, with Clausen functions ``\operatorname{Cl}_m`` and ``\operatorname{Re}\operatorname{Li}_m``: ``\int x \tan x`` |
| LP | any | ``\log^j(x)\, L(wx)/x``, ``L`` = `atan`, `log`, `li2` | polylogarithms by parts: ``\int \operatorname{atan}(x)/x = \operatorname{Ti}_2(x)`` |
| AT | any | `atan(u)` | ``u = \tan t`` |
| AP | any | ``A \cdot L^k`` with ``L`` an inverse function or `log` | by parts, ``\int A L^k = Q L^k - k\int Q L^{k-1} L'`` |
| HS | `NotElementary` | ``x^m(α + βx^n)^q``, ``\sin^p \cos^r``, symbolic exponents | ``{}_2F_1`` terms |
| EH | `NotElementary` | ``e^{ax} R(\cos bx, \sin bx)`` with the poles of ``R(E)``, ``E = e^{ibx}``, in ``ℚ(i)`` | partial fractions in ``E``. Each pole gives ``\int e^{ax}/(1 - E/r)^k = e^{ax}\,{}_2F_1(k, s; s+1; E/r)/a`` with ``s = a/(ib)``. The real part is printed with `rehyp2f1` and `imhyp2f1` (``\int e^x/(1 + \cos x)``) |
| H3, H4 | `NotElementary` | ``x^s e^{bx + d}``, ``x^s \sin``, ``x^s \cos`` | incomplete ``Γ`` terms |
| US | any | ``f = G(u)\,u'`` for a subterm ``u`` (and the partner ``\sinh v`` of ``\cosh v``, ``\sin v`` of ``\cos v``, …) | derivative-divides, below. With ``u = \sinh v``, even powers of ``\cosh v`` are ``(1 + u^2)^k``, and so on |
| NS | any | a radical with an inner radical ``\sqrt{R(x)}`` | ``x = X(u)`` that rationalizes the inner radical |
| CS | any | nested radicals with coefficients in ``ℚ(\sqrt d)`` | ``x = σy`` (``σ = 1, d, 1/d``). Each radicand is written as ``κ P_0`` with ``P_0`` over ``ℚ``, so ``\sqrt{κ}`` comes out: in ``ℚ(\sqrt d)``, or ``\sqrt b\, d^{1/4}`` for ``κ = b\sqrt d``. Step IT then takes out ``d^{1/4}``. Example: ``\sqrt{\sqrt2 + \sqrt x + \sqrt{2 + \sqrt8\sqrt x + 2x}}`` |
| PP | any | ``\sqrt{g + c_1}``, ``\sqrt{g + c_2}`` of one term ``g`` | ``w = \sqrt{x + c_1} - \sqrt{x + c_2}`` for ``g = x``. Then ``\sqrt{x + c_1} = (w + k/w)/2`` and ``\sqrt{x + c_2} = (k/w - w)/2``, with ``k = c_1 - c_2``. For ``g = h(ax + b)`` (``h`` = sec, csc, sin, cos, tan, cot, exp, sinh, cosh), first ``u = g``. Example: ``\sqrt{\sqrt{\sec x + 1} - \sqrt{\sec x - 1}}`` |
| RC | any | ``R(x)\sqrt{P}^k``, ``P(x) = x^m S(x + s/x)`` | ``u = x + s/x`` |
| RY | any | one radical ``y = P^{1/n}`` with ``P`` in an `exp`/`log` tower | ``\int A_r y^r = B_r y^r`` with ``B_r' + (r/n)(P'/P) B_r = A_r``, a Risch differential equation in the tower |
| LS | any | a sum, or a quotient with a sum on top | term by term, grouping terms with the same radicals |
| Expr retry | term type without special functions | | the integrand as an `Expr`, special terms evaluated numerically |

If none of them answers, the original exception is rethrown.

The order matters in a few places. LP comes before AT because ``\int \operatorname{atan}(x)/x`` is
one ``\operatorname{Ti}_2``, not eight Clausen terms. CL, HS, H3 and H4 run only after a proof that
the integral is not elementary, since they produce special functions. LS comes last: the terms of a
sum can need different routes (``\int 1/x + (1 + 1/x)/(x + \log x)^{3/2}``: a log, then
``u = x + \log x``; Rubi 219), but splitting can also separate terms whose sum is elementary while
the parts are not, so it is tried only when the whole integrand has failed.

#### u-substitution (step US)

For a subterm ``u`` of ``f``, compute ``q = f/u'`` (``u'`` by the chain rule on terms). Parse
``q`` into a tower in which ``u``, and every subterm whose `x` occurs only inside ``u``, is an
opaque constant. If ``q`` is a constant there, then ``f = G(u)u'`` with ``G`` the constant printed
with ``u ↦ x``: integrate ``G`` in ``x`` and substitute ``x ↦ u`` in the answer. Radicals extend
the test: for ``u = v^e`` also ``v = U^{1/e}``, and for ``u = x^k`` also ``x^{mk} = U^m``. For
``v = a + bθ`` with ``θ`` a log or exp, ``θ`` is replaced by ``(U^m - a)/b`` wherever it occurs,
so ``v`` written another way is still seen as ``U^m``.

#### Substituting back

A substitution step integrates in ``u`` and maps the answer back with ``u ↦ \text{back}(x)``
(`subst_answer`). The elementary part is a term and is mapped directly; RootSums are mapped by
attaching the back-substitution as their argument (`RootSum`) or to their coefficients
(`TermRootSum`, `ScaledRootSum`).

## Answers

### Exact results

`integrate_el` returns an `ElemIntegral`:

- `v`, the rational part, an element of the tower;
- `logs`, pairs ``(c, w)`` for ``c \log w``;
- `atans`, pairs ``(c, u)`` for ``c \operatorname{atan} u``;
- `quads`, the terms with irrational constants: `TowerQuadLog`, ``β\sqrt d \log((U + \sqrt d V)/(U - \sqrt d V))``;
  `TowerQuadAtan`; RootSums (`TowerRootSum`, `BaseRootSum`); real forms of quartic RootSums
  (`TowerRealForm`); special-function terms (`SpecialTerm`, `DilogTerm`, `DilogPairTerm`,
  `DilogQuadTerm`, `DilogGroup`).

For a rational function, `integrate_rational` returns a `RationalIntegral` with the same parts over
``C(x)`` plus the unresolved residue factors that become RootSums.

### Building terms

A `Builder` carries `build(op, args...)`, `lift(n)`, the variable term, and the constant generators.
`to_term` writes each part with `mk(b, :log, …)` and friends; `cterm` writes constants, with
``\sqrt d`` kept symbolic and each generator printed as what it stands for (the user's symbol,
``e``, ``\log 2``). `auto_build` and `auto_lift` choose defaults for the term type of the
integrand: operations are called as functions, and for SymbolicUtils, constants such as
``\sqrt 2`` are built with `TermInterface.maketerm` so they stay unevaluated.

### RootSums and numerically evaluated terms

The user's packages have no RootSum, and many have no ``{}_2F_1`` or ``Γ(s, x)``. When an answer
needs one, `risch_integrate` returns an `IntegralWithRootSums`: an elementary part (a term) plus a
list of objects that the package evaluates numerically:

- `RootSum{C}`: over the base field, ``\sum α \log W(α, x)``, evaluated at the roots of ``Q``.
- `TermRootSum`: a RootSum inside a tower, its coefficients written as terms.
- `ScaledRootSum`: a RootSum times a term (from step IT or substitutions).
- `HypTerm`, `GammaTerm`, `KummerTerm`, `TrigPowerTerm`: ``{}_2F_1`` and ``Γ`` terms.
- `ExprTerm`: a special-function term of an answer built through `Expr` (the `Expr` retry).

The object is callable: `F(a)` evaluates the whole antiderivative at ``x = a``, and
`rs_value_continuous` follows a continuous branch along the real line.

### Real forms of logarithms

Besides the Step 7 real forms, steps RL, EL and TL choose the arguments of logarithms in answers of
substitutions so that they are real where the substitution is real. Step EC does the same at the
base of real forms over ``ℚ(i)(\sqrt d)``.

## Verification

Every answer is checked before it is returned:

- In a tower: `check_tower(T, n, res, f)` differentiates the `ElemIntegral` with the tower
  derivation and compares with ``f``, exactly.
- For a rational function: `check_result`. With RootSums, the derivative of
  ``\sum α \log W(α, x)`` is computed exactly in ``ℚ(x)`` as ``\operatorname{Tr}(z\,∂_xW\,N/W)/N``
  with ``N = \operatorname{res}_z(Q, W)``, the trace computed from power sums of the roots.
- Real forms and real-log rewrites are checked again after the rewrite.
- A substitution checks its own identities exactly (``g(s(θ))\,s' = R`` in step MR,
  ``H(x + s/x) = h`` in step RC, ``\tilde U_j(s(θ)) = U_j``) and integrates the substituted integrand,
  which is itself checked. The chain rule then makes the composed answer an antiderivative.
- Special-function terms carry their exact derivatives into the check.

`verify = false` skips the final checks (not the internal identity checks of substitutions).

The checks are formal: they hold as identities of expressions. Branch questions (which square root,
which logarithm) are handled by the conventions above, not by the check.

## Errors

| Exception | Meaning |
|:----------|:--------|
| `NotElementary` | the integral was proved to have no elementary antiderivative, and no special-function form used by the package was found |
| `RischNotImplemented` | the integrand is outside the cases implemented; no decision |
| `RischError` | an internal check failed: a bug |

`NotElementary` is thrown only from decision procedures that are complete for their case: the
residue criterion, the Risch differential equation without unresolved cancellation, Liouville's
theorem on a hyperelliptic or Kummer curve. A substitution that fails does not prove anything, so
substitution steps return `nothing` or rethrow `RischNotImplemented`.

Internally, `Restart`, `NewConstants` and `NeedComplex` are control flow for `build_tower`.

## Recursion and global switches

Several steps call `risch_integrate` on a transformed integrand. Re-entry into the same step is
blocked by a flag:

| Flag | Prevents |
|:-----|:---------|
| `USUB_DEPTH` | u-substitutions nested more than two deep |
| `RECIPROCAL` | a reciprocal substitution inside another |
| `TOWER_RADICAL` | step RY inside step RY |
| `EXPR_RETRY` | nested `Expr` retries |
| `OPAQUE_CONST_RADICALS` | (set) constant radicals as opaque constants inside step PR |
| `HYP_ANSWERS` | (switch) set to `false` to get `NotElementary` instead of ``{}_2F_1``/``Γ`` answers |

## A few traces

**``\int 1/(x^3 + 1)``.** No radicals, no trigonometry: the tower is ``ℚ(x)``. Hermite reduction
leaves ``1/(x^3 + 1)``. The resultant has the rational root ``1/3``, giving
``\frac13 \log(x + 1)``, and a quadratic factor with roots ``-\frac16 ± \frac{\sqrt 3}{6} i``, giving
``-\frac16 \log(x^2 - x + 1) + \frac{\sqrt3}{3}\operatorname{atan}\frac{2x - 1}{\sqrt 3}``. With `Expr` terms:

```
1//3 * log(1 + x) + -1//6 * log(1 + -1x + x ^ 2) + 1//3 * sqrt(3) * atan(sqrt(3) * (-1//3 + 2//3 * x))
```

**``\int x e^x/(1 + x)^2``.** The tower is ``ℚ(x)(θ)``, ``θ = e^x``. The integrand is
``a θ`` with ``a = x/(1 + x)^2``; the Risch equation ``y' + y = a`` has the rational solution
``y = 1/(1 + x)``, so the integral is ``e^x/(1 + x)``, printed `(1 / (1 + x)) * exp(x)`.

**``\int e^{x^2}``.** The Risch equation ``y' + 2xy = 1`` has no rational solution, so the integral
is not elementary. Step 8a finds the quadratic exponent at the base:
``\frac{\sqrt π}{2}\operatorname{erfi}(x)``, printed `(sqrt(π) / (2 * sqrt(1))) * erfi(sqrt(1) * x)` (the
general formula ``\sqrt π/(2\sqrt{\lvert A \rvert}) \operatorname{erfi}(\sqrt{\lvert A \rvert}(x + h))`` with ``A = 1``, ``h = 0``, not simplified).

**``\int \sqrt{x^2 + 1}``.** One quadratic radicand: an Euler substitution
``\sqrt{x^2 + 1} = t - x`` over ``ℚ``, a rational integral in ``t``, with ``t`` printed as
``\sqrt{x^2 + 1} + x``. Step EL keeps the logarithm's argument positive:

```
(-1//8 + 1//8 * (sqrt(x ^ 2 + 1) + x) ^ 4) / (sqrt(x ^ 2 + 1) + x) ^ 2 + 1//2 * log(sqrt(x ^ 2 + 1) + x)
```

**Rubi 218.**
``\int \big(3(x + e^x)^{1/3} + (2x^2 + 3x)e^x + 5x^2\big)/\big(x(x + e^x)^{1/3}\big)``. The radicand
``x + e^x`` is not rational in `x`, so `integrate_radical` refuses, and none of MR, NR, PW or DN
apply. In the fallback chain, step RY splits the integrand as ``3/x + A\,y^{-1}`` with
``y = (x + e^x)^{1/3}``, rewrites ``y^{-1} = y^2/(x + e^x)``, and solves
``B' + \frac23 \frac{1 + e^x}{x + e^x} B = \frac{(2x + 3)e^x + 5x}{x + e^x}`` in ``ℚ(x)(e^x)``:
``B = 3x``. The radical-free part ``3/x`` integrates as usual:
``3x(x + e^x)^{2/3} + 3\log x``.

**``\int \sqrt{-1 - x^2}``.** The radicand is never positive (step NP):
``\sqrt{-1 - x^2} = i\sqrt{1 + x^2}`` with ``i = \sqrt{-1}`` opaque. The Euler substitution handles
``\sqrt{1 + x^2}``, and ``\sqrt{-1}`` stays a factor of the answer: the previous answer times
`sqrt(-1)`, with ``\sqrt{1 + x^2}`` written `sqrt(-1 * (-1 - x ^ 2))`.

**``\int \operatorname{atan}(x)/x``.** The tower ``ℚ(x)(\operatorname{atan} x)`` proves the
integral not elementary. In the fallback chain, step LP writes ``\operatorname{atan} x`` as
``\operatorname{Im} \operatorname{Li}_1(ix)``, so the integral is
``\operatorname{Im}\operatorname{Li}_2(ix) = \operatorname{Ti}_2(x)``, printed
`impolylog(2, x, 1//2 * π)`.

**``\int x \tan x``.** Not elementary. Step CL integrates by parts over ``ℚ(i)``,
``θ = e^{2ix}``: ``G_1 = \int \tan x`` has the logarithm of ``θ + 1``, whose root ``-1`` is on the unit
circle, and ``\int G_1`` gives a Clausen function:

```
-1//2 * (x * log(2 + 2 * cos(2x))) + -1//2 * clausen2(2x + -1 * π)
```

## Coverage and testing

The test suite (`test/`) runs most cases with SymEngine terms (`run_tests`) and the newer steps
with `Expr` terms, checking answers numerically at points of their domain, and checks refusals by
exception type. It also covers the tower machinery directly
(`test_tower.jl`, `test_risch.jl`), the problems from Apostol's *Calculus* (`test_apostol.jl`), the
`@integrate` macro, and compilation of the first call.

Coverage is measured on the 1680-problem sample from the Rubi test suite, scored by numeric
differentiation of each answer; the README has the current numbers and a comparison with Giac and
SymPy. Most of the steps after Step 8 in the tables above were added to close specific Rubi
failures, and their comments cite the Rubi problem numbers.

## Open questions and limits

- **The algebraic Risch algorithm** is implemented only in pieces: one radical of a rational
  function (substitution, Euler, hyperelliptic Hermite reduction and Liouville without residues),
  Kummer extensions with a restricted log part, two square roots (biquadratic), and nested square
  roots in two special forms. General algebraic function fields (Trager's algorithm) are not.
- **Cancellation cases** of the Risch differential equation (Bronstein §6.6) are recognized but not
  solved; integrands that need them are refused.
- **Complex constants** in the input are opaque (``\sqrt{-1}``) rather than elements of ``ℚ(i)``:
  answers are correct identities, but ``i^2 = -1`` is not used to simplify them.
- **Parameters** are capped in number and take signs from fixed values. Answers that depend on the
  sign of a parameter expression hold for one choice of signs only.
- **Output form.** Answers are not simplified beyond what the algorithm produces; leaf counts are
  often larger than Rubi's optimal answers. Simplification is the caller's CAS's job.

## Step index

| Code | Where | Short description |
|:-----|:------|:------------------|
| 7 | `real_form.jl` | trigonometric input over ``ℚ(i)``, real forms of answers |
| 8a | `special_functions.jl` | `Ei`, `erf`, `erfi`, `li` for non-elementary exp/log integrals |
| 9a | `risch_de.jl` | Risch differential equation with arbitrary denominators |
| 9d | `parametric_rde.jl` | parametric Risch differential equation |
| 10a | `radicals.jl` | radicals of a linear-fractional radicand |
| 10b, 10c | `euler_substitutions.jl` | square roots of quadratics (Euler) |
| 10d | `euler_substitutions.jl` | square roots of two linear polynomials |
| 10e | `radicals.jl` | square roots of rational constants |
| AC | `inverse_trig.jl` | `acot`, `acsc`, `asec` rewritten |
| AP | `inverse_trig.jl` | by parts for ``A L^k`` |
| AS | `inverse_trig.jl` | `asin`, `acos` by ``u = \sin t`` |
| AT | `inverse_trig.jl` | `atan(u)` by ``u = \tan t`` |
| BQ | `biquadratic.jl` | two square roots, biquadratic splitting |
| CL | `clausen.jl` | ``x^p R(\sin, \cos)`` with Clausen functions |
| DL, LF, DC | `dilogarithms.jl` | dilogarithms; logs of quadratics with complex roots |
| DN | `denest.jl` | denesting square roots |
| EC, EL, RL, TL | `real_log_arguments.jl` | real arguments of logarithms |
| EP, LS | `linearity.jl` | exponent merging; term-by-term integration |
| H1, HS | `hypergeometric.jl`, `hyp_symbolic.jl` | ``{}_2F_1`` answers |
| H3, H4 | `gamma_terms.jl` | incomplete ``Γ`` answers |
| EH | `exp_trig_hyp.jl` | ``e^{ax} R(\cos bx, \sin bx)`` with ``{}_2F_1`` terms |
| IT | `risch_integrate.jl` | constant factors out; iterated integrals |
| LP | `polylog_parts.jl` | polylogarithms by parts |
| MR, PW, NR | `monomial_radicals.jl` | radicals of functions of a monomial; inner linear radicals |
| NP | `radicals.jl` | square roots of never-positive radicands |
| NS | `nested_subst.jl` | nested radicals by substitution |
| CS | `constant_scaling.jl` | nested radicals over ``ℚ(\sqrt d)``: scaling and constant factors out of radicands |
| PP | `nested_subst.jl` | pairs of square roots ``\sqrt{g + c_1}``, ``\sqrt{g + c_2}`` |
| PL, PR, PS | `param_radicals.jl` | parameters: linearity, radicands, scaling |
| BN | `param_radicals.jl` | binomial denominators ``x^n + c``: ``x = \lvert c\rvert^{1/n} u`` |
| PC | `precompile.jl` | precompile workload |
| R2, NR | `quartic_residues.jl` | real forms of quartic residues, nested radicals in them |
| BQ4 | `quartic_residues.jl` | even quartics ``x^4 + bx^2 + c`` with nested real forms |
| RC | `reciprocal_subst.jl` | ``u = x + s/x`` |
| RE, RT, RF | `constant_fields.jl`, `tower_rootsums.jl`, `tower_real_forms.jl` | RootSums over parameter fields and in towers, their real forms |
| RP, SQ | `factoring.jl`, `radicals.jl` | radicands that are powers; repeated factors |
| RY | `tower_radicals.jl` | a radical of a tower element |
| SY | `tower_terms.jl` | parameters and opaque constants |
| TA | `tower_terms.jl`, `monomial_integration.jl` | `atan` levels |
| TS | `bioche.jl` | Bioche's rules |
| TS2 | `risch_integrate.jl` | addition formulas for shifted trigonometric arguments |
| US | `u_substitution.jl` | u-substitution |
| WR | `tower_terms.jl` | wrapped leaves refused |
