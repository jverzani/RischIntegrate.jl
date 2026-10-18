# Plan: "Symbolic Integration II": algebraic integrands

The package follows Bronstein's *Symbolic Integration I: Transcendental Functions*. Bronstein's
planned second volume (algebraic and mixed algebraic–transcendental integrands) was never written.
This branch (`si2`) implements a usable part of it. The literature behind each phase is listed in
the last section.

## Progress

* Phase 1: done, tests green (2026-10-18). `src/hyperelliptic.jl`, hooked from
  `integrate_radical` (one polynomial radicand, squarefree, degree ≥ 3, index 2, no constant
  radicals). Test set "Hermite reduction on y² = a, genus ≥ 1 (SI2 phase 1)" in
  `test_integrate.jl`. `1/√(x³+1)` and `√(x⁶+1)` now raise `NotElementary`.
  Fix (with phase 2): the residue at ∞± is the x⁻¹ coefficient of P/y (Laurent series of 1/y,
  `hyp_res_inf`), not just the x^{m−1} coefficient of P.
* Phase 2, residues at infinity only: done, tests green (2026-10-18).
  * `hyp_pell`: the polynomial Pell equation by the continued fraction of √a; the unit is made primitive.
  * `hyp_dlog_unit`: du/u is checked exactly, then λ = res(P)/res(du/u).
  * Genus 1 is decided: ∞₊ − ∞₋ is a ℚ-point of an elliptic curve, so by Mazur its order is ≤ 12. No
    unit with deg p ≤ 12 means `NotElementary`.
  * Genus ≥ 2: search up to deg p ≤ 60, else `RischNotImplemented`.
  * Not yet: lc(a) not a square (∞ is a place of degree 2). Finite residues: next.
  * Trager's ∫x/√(x⁴+10x²−96x−71) gives his degree-8 unit.
* Phase 2, rational residues at finite places: done, tests green (2026-10-18). `hyp_log_part`.
  * `hyp_finite_residues`: r² ≡ R²/(D′²a) mod each irreducible factor of D. The places with residue +r
    are where y ≡ R/(rD′) mod G_r.
  * b = gcd of all residues (∞₊ included), Δ = Σ (r/b)(P_r − σP_r) + (ρ₊/b)(∞₊ − ∞₋).
  * For N = 1…12, `hyp_divisor_unit` solves for v = p + qy vanishing to order 2N·n at P_r, with
    the pole orders at ∞± fixed. These are linear conditions: a Hensel lift of √a mod G^e, and the
    Laurent series of y at ∞. Riemann–Roch gives dimension ≤ 1, and dimension 1 iff NΔ is principal.
    Then u = v/ΠG^{Nn} and λ = b/N.
  * The system is first solved mod 2³¹−1 (`ModP`): a trivial kernel mod p proves a trivial kernel over
    ℚ, so the exact solve runs only when a solution is likely.
  * Genus 1: no N ≤ 12 gives `NotElementary`, since Δ is a ℚ-point of the Jacobian (Mazur). Genus ≥ 2:
    `RischNotImplemented`.
  * Bug found on the way: the conditions at ∞ need the series of y (A^{1/2}), not of 1/y.
  * Not yet: irrational or algebraic residues (e.g. ∫1/((x²+1)√(x³+1))). Also a faster test for
    large multiples: Cantor's algorithm / Mumford representation. And a torsion bound for genus ≥ 2
    (counting points over 𝔽_{pᵏ}).

## Where we start

Radicals today (`radicals.jl`, `euler_substitutions.jl`) are handled only when the curve has
**genus 0**: a rational substitution x = φ(t) turns the integrand into a rational function of t,
and the transcendental machinery takes over. Covered: one radicand `(ax+b)/(cx+d)` with any index,
`√(quadratic)`, two `√(linear)`, and square roots of constants. Everything else raises
`RischNotImplemented`, e.g. `1/√(x³+1)`, `x/√(x⁴+1)`, `1/(x+1)^(1/3)·…` with a nonlinear radicand,
`√(log x)`.

So the new work starts at **genus ≥ 1**. Two problems have to be solved:

1. **Case 1, the algebraic part (Hermite reduction on a curve).** Reduce ∫ω to an algebraic
   function plus a remainder with only simple poles. If the remainder has no residues, it is either
   0 (answer found) or provably not elementary.
2. **Case 2, the logarithmic part (divisors and torsion).** If the remainder has residues, the
   answer, if any, is `Σ cᵢ log uᵢ` where each `uᵢ` has a prescribed divisor (up to a multiple n).
   Find the `uᵢ` or prove that no multiple of the divisor is principal.

Case 1 comes first: it is mechanical, it already decides many integrals (e.g. ∫1/√(x³+1) is not
elementary, ∫ (stuff)/(x³+1)^(3/2) = algebraic), and Case 2 needs its output.

## Phase 1: hyperelliptic curves y² = a(x) (Case 1)

Scope: integrands that are rational in x and y = √a, a ∈ ℚ[x] squarefree with deg a ≥ 3 (one
radicand; exponents k/2). The integral basis is {1, y} at every finite place, so no integral-basis
algorithm is needed yet.

* `HypEl` = p + q y (p, q ∈ ℚ(x)), field operations (inverse via the norm p² − q²a), and a term
  parser into it (`x`, rationals, + − * / ^, `sqrt(a)`, `a^(k/2)`).
* ∫p is a rational integral (existing code). By the involution y ↦ −y, ∫(p + qy) is elementary iff
  ∫qy is, so the rest works on ω = q y dx = B/(D y) dx.
* **Finite Hermite reduction.** d(C y / Vᵏ) = (C′aV − kCV′a + CVa′/2)/(V^{k+1} y).
  * For V coprime to a: reduce V^m → V^{m−1} while m ≥ 2 (solve C mod V, as in Bronstein 2.2).
  * For V | a (ramified places): the same identity with a = VW lowers V^m → V^{m−1} for all m ≥ 1,
    because the factor (1/2 − k) never vanishes. These poles disappear entirely.

  Result: ω = d(g y) + (P + R/D)/y with D squarefree and coprime to a.
* **Reduction at infinity.** d(xᵏ y) = (k x^{k−1} a + xᵏ a′/2)/y lowers deg P to ≤ deg a − 2.
* **Decision.**
  * Residues are ±R(α)/(D′(α)√a(α)) at the roots of D. At infinity there are none for odd deg a,
    and ±(coefficient of x^{deg a/2 − 1} in P)/√lc(a) for even deg a.
  * Remainder 0: the answer is g·√a (+ the rational part).
  * Remainder nonzero with no residues: **NotElementary**. Liouville plus the residue argument give
    ω = dv. Then v has no finite poles, so v = R₁ + R₂y with polynomials Rᵢ, and deg dv > deg P.
  * Otherwise: Case 2.
* Verify exactly: (g a′/2 + g′a) = (q − remainder)·a.
* Hook: `integrate_radical`, single radicand, index 2, polynomial radicand of degree ≥ 3 (after
  `radicand_power`). Later: rational radicands N/Dd (y = √(N·Dd)/Dd), square factors of a.

## Phase 2: the log part on hyperelliptic curves (Case 2)

* Residues: the roots of Res_x(R − z·D′·y…), i.e. of the polynomial whose roots are R(α)²/(D′(α)²a(α)).
  Start with **one ℚ-dimension of residues** (all residues ±r·{1}), then general ℚ-bases of residues
  (one divisor per basis element, as in Rothstein–Trager over algebraic numbers).
* Divisor Δ = Σ (P₊ − P₋), where P₊ is the place y ≡ S(x) = R/(r D′) mod D, plus ∞₊ − ∞₋ for even deg a.
  Look for u = p + q y with div(u) = nΔ:
  * u vanishes to order n at P₊: p + q·Yₙ ≡ 0 mod Dⁿ, with Yₙ the Hensel lift of √a mod Dⁿ starting
    at S. This is linear in the coefficients of p and q.
  * Norm p² − q²a = c·Dⁿ, with degree bounds for p and q from n·deg D and the order at ∞±.
  * Pure infinity divisors (D = 1) give the **polynomial Pell equation** p² − q²a = c. Solve it by
    the continued fraction of √a (or by the same linear algebra).
    Example: ∫ x/√(x⁴+1) = ½ log(x² + √(x⁴+1)).
* Search n = 1, 2, … up to a torsion bound. On success, return (r/n) log u, subtract, and recheck the
  residue-free rest (it must be 0, or NotElementary).
* **Proving non-elementarity** (no n works) needs a bound on the torsion order:
  * Genus 1 (deg a ∈ {3, 4}): the order divides #E(𝔽ₚ) for primes p ≥ 3 of good reduction. Count
    points by brute force for a few small p and take the gcd (Nagell–Lutz / reduction).
  * Higher genus: #Jac(𝔽ₚ) from point counts over 𝔽_{pᵏ}, k ≤ g (zeta function). Until that exists,
    an exhausted search raises `RischNotImplemented`, not `NotElementary`.
* Output: real form of log(p + q√a); residues in ℚ(i) give atan-like terms as in the rational case.

## Phase 3: simple radical extensions yⁿ = a (Cases 1 + 2)

* Integral basis for yⁿ = a, a = Π aᵢ^i: wⱼ = yʲ / Π aᵢ^⌊ij/n⌋ (Bronstein's thesis). No general
  algorithm is needed.
* Trager's Hermite reduction w.r.t. that basis. Normalisation at infinity (Trager's "normal at
  infinity" basis) is required for the residue-free ⇒ (0 or non-elementary) decision.
* Log part as in phase 2, with places from the factorisation of a and D and the Puiseux expansions
  at them.
* Covers cube roots of cubics, (x³+1)^(1/3), x/(x⁴+1)^(1/4), etc.

## Phase 4: general algebraic curves (optional, large)

* Integral bases by Trager's algorithm (or van Hoeij's) for F(x, y) = 0.
* Puiseux expansions, places at infinity, Riemann–Roch spaces (for Case 2 in general).
* Bronstein's lazy Hermite reduction (avoids the full integral basis).
* Several radicands of genus ≥ 1 (√(x³+1)·√x … as one curve with a primitive element).

## Phase 5: mixed algebraic–transcendental (Bronstein's thesis, 1990 JSC paper)

* Algebraic extensions on top of a monomial tower: √(log x), √(1 + eˣ), log(x + √(x³+1)).
* The Risch DE and parametric problems over an algebraic extension (degree / denominator bounds,
  cancellation cases redone over K(θ)[y]).
* Structure theorems with algebraic elements (is the new monomial really new?).

## Order and acceptance tests

1. Phase 1, tested against:
   * ∫1/√(x³+1) → NotElementary.
   * ∫x/√(x³+1) → NotElementary (a second-kind differential).
   * ∫ d/dx(x/√(x³+1)) → x/√(x³+1).
   * ∫ (3x²)/(2√(x³+1)) → √(x³+1).
   * ∫1/(x√(x³+1)) → RischNotImplemented (log part; actually elementary, phase 2).
   * Integrands with rational parts.
2. Phase 2:
   * Pell first (∫x/√(x⁴+1), ∫ (x²−1)/((x²+1)√(x⁴+1)) type).
   * Then finite divisors (∫1/(x√(x³+1)) = (1/3) log((√(x³+1)−1)/(√(x³+1)+1))).
   * Then the genus-1 torsion bound.
   * Classic tests: Chebyshev's pseudo-elliptic integrals, Trager's ∫ x/√(x⁴ + 10x² − 96x − 71).
3. Phases 3 and 5 when 1 and 2 are solid; phase 4 only if needed.

## References

* M. Bronstein, *Integration of elementary functions*, J. Symb. Comp. 9 (1990), and his thesis
  (Berkeley, 1987): simple radical extensions, mixed towers.
* B. Trager, *Integration of algebraic functions*, PhD thesis, MIT (1984): integral bases,
  Hermite reduction, the log part via divisors.
* J. H. Davenport, *On the integration of algebraic functions*, LNCS 102 (1981): torsion,
  reduction mod p.
* M. Bronstein, *The lazy Hermite reduction*, INRIA RR-3562 (1998).
* R. Risch, *The solution of the problem of integration in finite terms*, Bull. AMS (1970).
