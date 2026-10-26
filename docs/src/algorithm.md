# How it works

The integrand is parsed into an exact differential field and integrated there by the Risch
algorithm, following Bronstein, *Symbolic Integration I*. The answer is checked by
differentiation in the same field, then rebuilt as a term of the user's package. The
[Design notes](design.md) follow an integrand through every step in detail.

## The steps

1. **Rational functions** ``ℚ(x)``: Hermite reduction (Bronstein §2.2) gives the rational part,
   the Rothstein–Trager resultant the logarithmic part. Quadratic residues give `log` and `atan`
   terms over ``ℚ(\sqrt d)`` (with Rioboo's LogToAtan for real, continuous `atan` terms); quartic
   residues are written with real radicals when possible; other residues of degree greater than 2
   give a `RootSum`.
2. **Towers** ``ℚ(x)(θ_1)…(θ_n)``: `exp`, `log` and `atan` are monomials over the field below
   them; `sin`, `cos`, `tan`, … are rewritten with complex exponentials over ``ℚ(i)``. The
   structure theorems (Bronstein ch. 9) decide whether a new `exp` or `log` is algebraically
   independent of the previous ones.
3. **Integration in a monomial extension** (Bronstein ch. 5): Hermite reduction with the tower's
   derivation, the residue criterion for the logarithmic part, and the polynomial part through
   the **Risch differential equation** ``y' + f y = g`` (ch. 6) and its parametric form (ch. 7).
   When there is no solution, the integral is proved to be non-elementary (`NotElementary`).
4. **Real forms**: answers over ``ℚ(i)`` are written as real terms, continuous on the real line
   where the integrand is (Bioche's rules choose simpler substitutions for trigonometric
   integrands).
5. **Constants**: the constant field can be ``ℚ``, ``ℚ(i)``, ``ℚ(\sqrt d)`` or a field of
   symbolic parameters, `e` and logarithms of numbers.
6. **Substitutions** reduce other integrands to these cases: radicals of a linear-fractional
   radicand, Euler substitutions for square roots of quadratics, `asin`/`acos` by
   ``u = \sin t``, and u-substitution (derivative-divides).
7. **Special functions**: non-elementary integrals of the forms ``∫ e^{u}/v``, ``∫ e^{-x^2}``,
   ``∫ \sin(x)/x``, ``∫ \log(x)/(x - a)``, … are written with `expinti`, `erf`, `erfi`,
   `sinint`, `cosint` and `li2`.

## The source files

The sources in `src/` are included by `src/RischIntegrate.jl` in this order:

| File | Contents |
|:-----|:---------|
| `core.jl` | number and constant types, the error types |
| `polynomials.jl` | dense univariate polynomials: Euclid, extended gcd, squarefree factorisation, resultant |
| `fractions.jl` | the fraction field of a polynomial ring |
| `factoring.jl` | integer factoring, rational roots, factorisation over ``ℚ`` (Cantor–Zassenhaus) |
| `number_fields.jl` | ``ℚ(i)`` and ``B(\sqrt d)`` |
| `hermite_reduction.jl` | Hermite reduction |
| `rothstein_trager.jl` | the logarithmic part of a rational function |
| `log_to_atan.jl` | Rioboo's LogToAtan |
| `quartic_residues.jl` | real forms of quartic residues, nested radicals |
| `term_input.jl`, `term_output.jl` | from terms to exact elements and back |
| `tower.jl` | towers of monomials and their derivation |
| `constant_fields.jl` | the constant fields |
| `structure_theorems.jl` | `exp` and `log` of tower elements (Risch's structure theorems) |
| `tower_terms.jl` | building the tower of an integrand |
| `rde_base.jl`, `risch_de.jl` | the Risch differential equation |
| `parametric_rde.jl` | the parametric Risch differential equation |
| `monomial_integration.jl` | integration in a monomial extension |
| `dilogarithms.jl` | dilogarithms |
| `exp_trig_polynomials.jl` | polynomials times exponentials and trigonometric functions |
| `special_functions.jl` | non-elementary integrals with special functions |
| `real_form.jl` | real forms of answers over ``ℚ(i)`` |
| `radicals.jl`, `euler_substitutions.jl` | radicals by substitution |
| `rootsum.jl`, `tower_rootsums.jl`, `tower_real_forms.jl`, `rootsum_numerics.jl` | RootSums: construction, real forms, numeric evaluation |
| `bioche.jl` | Bioche's rules |
| `sturm.jl` | real roots and signs (Sturm sequences) |
| `inverse_trig.jl` | `asin`, `acos`, `acot` |
| `u_substitution.jl` | u-substitution |
| `risch_integrate.jl` | the entry point |
| `real_log_arguments.jl` | real arguments of logarithms in substitution answers |
| `precompile.jl` | the precompile workload |
