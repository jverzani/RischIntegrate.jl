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
* Phase 2, quadratic irrational residues: done, tests green (2026-10-18).
  * The residues on each factor of D are ±s√d (r² ≡ c mod F, c ∈ ℚ). They are grouped by the class
    d ∈ ℚ*/ℚ*², and ∞₊ is in the class of lc(a). The √d are ℚ-independent, so each class needs its own
    torsion divisor Δ_d over K = ℚ(√d).
  * The same solver runs over K: `hyp_divisor_unit` is generic, and `HypEl{F}` / `ModP{p}` are
    parametric. The filter prime p ≡ 3 mod 4 is chosen so that d is a square mod p.
  * Output: for d > 0, λ log u with sqrt(d) symbolic. For d < 0, u·ū is constant, so
    λ log u = −δβ atan(δB/A). Both are checked exactly (`hyp_check_dlog`, `hyp_check_norm`).
  * Genus 1 is decided with N ≤ 12 for ℚ (Mazur) and N ≤ 18 for ℚ(√d) (Kamienny–Kenku–Momose).
  * Residues only at a degree-2 place at ∞ (lc(a) not a square) go through the same path, e.g.
    ∫x/√(2x⁴+1).
* Phase 2, torsion orders by reduction mod p; genus 2; residues of degree 4 (decision): done, tests
  green (2026-10-18). `hyp_torsion_order`.
  * Take a prime 𝔭 of residue degree 1 over p ≥ 7 where y² = a has good reduction. Reduction is
    injective on Jacobian torsion (Katz), so a torsion Δ has the same order N mod 𝔭.
  * The order mod p is the least N | #J(𝔽_p) with NΔ̄ principal, found with the same linear system
    over 𝔽_p. #J = #C(𝔽_p) for genus 1, and (N₁² + N₂)/2 − p for genus 2 (`hyp_count1/2`). Genus ≥ 3
    uses the Weil bound.
  * Two primes with different orders give `NotElementary`, for any genus. Equal orders leave one exact
    test at N. This replaces the N ≤ 12/18 search, which stays as the fallback when no primes are found.
  * It also decides the Pell case for genus ≥ 2.
  * `ModP` has one global modulus (`with_mod`), so the code isn't recompiled per prime.
  * Degree-4 residues (`hyp_quartic_decision`): one quadratic factor F with r² ≡ h mod F not constant,
    and no residue at ∞. The residues are ℚ-dependent iff h² ≡ c and c/N(h) is a square. When they
    are independent, elementary iff P₁ − σP₁ is torsion, decided mod p.
    E.g. ∫1/((x²+1)√(x³+1)) is `NotElementary`.
* Phase 2, the log part for residues of degree 4: done, tests green (2026-10-18). `hyp_quartic_log`.
  * r₁² = h(α₁) is irrational, so L = ℚ(α₁, r₁) = ℚ(r₁) = ℚ[z]/(M), with α₁ = (z² − h₀)/h₁ and
    M ∝ F((z² − h₀)/h₁). `NFz`: one type with a global modulus (`with_nf`), like `ModP`.
  * With N from the orders mod p, `hyp_divisor_unit` runs over L for u = v/(x − α₁)^N with
    div(u) = N(P₁ − σP₁), at P₁ = (α₁, R(α₁)/(z D′(α₁))).
  * Log part: Σⱼ (rⱼ/N) log uⱼ = ½ Σ_{M(z)=0} (z/N) log U(z), with U = (p + q y)(x − α₂)^N (since
    1/(x − α₁) = (x − α₂)/F). Output: `ScaledRootSum(1/(2N), TermRootSum(M, …))`, whose coefficients
    are Pⱼ(x) + Qⱼ(x)√a.
  * If h(α₁) is a square in ℚ(α₁), M = M₁(z)M₁(−z): L = ℚ[z]/(M₁), factor 1, plus −(Σz) log F.
  * Exact checks: d log u over L, then the residue-free rest after subtracting ½Tr_{L/ℚ}((z/N)Pu)
    (computed from the power sums of M).
  * The assembly of the printed answer is not covered by the exact checks: a sign error in the
    −(Σz) log F term was caught only by the numerical test.
  * Test example: P₁ = (1+√2, (1+√2)√6), 4-torsion on y² = 3(x³ − x) (a twist of the 4-torsion
    point of y² = x³ − x).
* Phase 2, degree-4 residues mixed with other residues: done, tests green (2026-10-18).
  * `hyp_finite_residues` returns the classes and, separately, the quadratic factors with nonconstant
    h. Each such factor is handled on its own by `hyp_quartic_decision` / `hyp_quartic_log`, next to
    the classes and the residues at ∞.
  * Decoupling needs the residue span to be a direct sum (`hyp_residues_independent`). The argument
    is Kummer theory over K₁ = ℚ(√d, √e): different square classes of K₁* are K₁-independent.
    * Class residues lie in K₁. The pairs rⱼₖ = √hₖ(αⱼₖ) are certified to lie in other square
      classes than 1 and than the other factors, by one degree-1 prime with a non-residue per pair.
    * Inside one factor, r₁/r₂ ∉ ℚ is tested exactly. r₁/r₂ ∈ K₁ is possible and harmless, e.g. 3 − 2√2.
    * Square roots mod p are fixed per prime factor of the d, e (and −1), so the maps K₁ → 𝔽_p are
      consistent.
  * Uncertified or dependent cases give `RischNotImplemented`.
* Phase 2, dependent residues: done, tests green (2026-10-18).
  * Inside one pair, dependence is impossible: r₁/r₂ = q ∈ ℚ forces h(α₁) = q² h(α₂) and then h rational.
    So it is always between groups.
  * For a quadratic factor with r² = A + B√e and A² − eB² = n² a rational square, the residues are
    multiquadratic. Denesting gives r = √p₁ + (B/2p₁)√p₁√e_α with p₁ = (A+n)/2 (`hyp_split_quadratic`).
    That is one entry in class d₁ = [p₁] (places y ≡ S) and one in class d₂ = [p₁e] (places y ≡ εS,
    ε = ±1 over the two roots).
  * The class machinery then pools all residues of a class over all factors, with integer
    multiplicities. That resolves every dependency among multiquadratic residues, and the answers are
    logs and atans with √d instead of RootSums.
  * The RootSum path remains for non-multiquadratic quartic residues (A² − eB² not a square). It has a
    direct exact unit test, because no torsion example of that kind has been found yet.
  * Rubi's library was used as a source of integrands (`library_of_problems.jl` in
    RUBISymbolicIntegration.jl, parsed as Expr, not evaluated). There were 48 problems with √ of a
    polynomial of degree ≥ 3. No `NotElementary` contradicts an elementary Rubi answer.
  * Fixes found along the way:
    * Square roots mod p by Tonelli–Shanks. The filter for ℚ(√−1) looped forever, because it only
      looked at primes p ≡ 3 mod 4.
    * l mod p is not needed for classes without a residue at ∞.
    * Logs whose argument may be negative on the real domain (sampled) are printed as (λ/2) log(u²).
    * No `sqrt(1)` in atan terms.
* Gaps seen in Rubi's library:
  * Radicands with repeated factors (√((x−3)²(x+1)) is genus 0).
  * Two different radicands of degree ≥ 3.
  * Cube and fourth roots (phase 3).
  * Nested radicals.
* Next / not yet: non-multiquadratic quartic residues mixed with dependent ones; residues of degree > 4.
  * Residues of degree > 4 (a general ℚ-basis of the residue span).
  * Faster divisor arithmetic for large multiples (Cantor's algorithm / Mumford representation).
  * #J for genus ≥ 3 (counts over 𝔽_{pᵏ}, k ≤ g).

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
