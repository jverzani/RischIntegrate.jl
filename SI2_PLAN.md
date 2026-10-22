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
* Step SQ, radicands with repeated factors: done, tests green (2026-10-18). `radicals.jl`.
  * Square roots, u = s²w with w squarefree: the variable is Y = √u/s. Y² = w holds on every interval,
    whatever the sign of s (the principal √u is |s|√w).
    * deg w ≥ 3: Hermite reduction / log part with yterm = √u/s. `parse_hyp` accepts (k, sᵏ) from
      radval.
    * deg w = 1, 2: 10a / Euler, with u^(k/2) = s(φ)ᵏ·radpow(k) and `R = Yterm` in
      `euler_substitution`. The positivity list is empty (Y has no fixed sign), so sign-changing logs
      print as log(w²)/2.
    * w constant (√((x+1)²) = |x+1|): Y is locally constant, and ∫f = ∫f₀ + Y∫f₁. This fixed a
      pre-existing wrong answer for x < −1: the Euler parametrisation degenerates on one branch. With
      constant radicals (SymEngine's √2·√((x−1)²)): F± on the two branches √u = ±s√c, combined with
      sign(s) = (√u/s)/√c.
  * Index n ≥ 3, u = sⁿ(x−a)ʲ(x−b)ᵏ with n | j+k (or one linear factor), gcd(j, n) = 1: genus 0,
    u^(1/n) = s(x−b)^((j+k)/n)·v^(j/n) with v = (x−a)/(x−b) (10a). t is printed through u^(1/n) as
    T^{j′}/v^{e₀}. `integrate_root_repeated`.
  * Rubi scan (48 problems with √ or roots of degree ≥ 3): 34 OK, 1 NotElementary (consistent),
    13 RischNotImplemented.
* Step BQ, two square roots of different radicands (not both linear): done, tests green
  (2026-10-18). `biquadratic.jl`.
  * K = ℚ(x)(√a, √b) has Galois group V₄. f = f₀ + f₁√a + f₂√b + f₃√a√b, and the parts are the four
    character projections.
  * Projecting Liouville's form shows that ∫f is elementary iff every part is, each over its own
    quadratic subfield. So a `NotElementary` part proves the whole.
  * Each part goes back through `risch_integrate` (√a, √b, √(ab); steps SQ, 10a, Euler,
    hyperelliptic), and √(ab) is rewritten to √a√b in the answer. That is valid on every branch,
    since the answer only uses Y² = ab.
  * Bonus: ∫(√x + √(x+1) + √(x+2)) now works (x = t², then two roots). √x√(x²+1) is decided
    (genus 1).
* Phase 3a, products of radicals of any index (Hermite reduction and decision): done, tests green
  (2026-10-19). `kummer.jl`, the fallback when `integrate_radical` gives up.
  * Factor all radicands into pairwise coprime squarefree bases bₖ (primitive integer polynomials).
    An element is Σ g_e θ_e with θ_e = Π bₖ^eₖ, eₖ ∈ [0,1). Inverses of sums are computed by linear
    algebra on the subgroup generated by the support.
  * The θ_e are eigenvectors of the Kummer automorphisms, so ∫f is elementary iff every component
    is (as in step BQ).
  * Per component, θ′/θ = M/A:
    * Hermite reduction at V | A (coefficient rₖ − k ≠ 0; no residues there, by the roots-of-unity
      symmetry) and at V coprime to A.
    * Reduction at ∞ (coefficient lc(A)(k + ρ), ρ = Σ rₖ deg bₖ).
    * Residues at ∞ only when ρ ∈ ℤ (series of Π bₖ^(rₖ−1)).
    * A residue-free nonzero remainder is not elementary (v = Cθ, C a polynomial, degree argument).
  * Checked against Chebyshev's theorem on ∫xᵐ(1+2xⁿ)ᵖ: 504 integrals, n = 2…5, m = −3…4, 18
    exponents p. All 347 non-elementary cases are decided `NotElementary`, 131 of the 157 elementary
    ones are integrated, and the other 26 need the log part. No disagreement.
  * Constant factors of radicands must have rational powers. Answers are valid where every base is
    positive.
  * Rubi scan: 36 OK, 1 NotElementary, 11 RischNotImplemented: 10 need the log part (phase 3b), plus
    one nested radical.
* Phase 3b, the log part for one radical of index q ≥ 3: done, tests green (2026-10-19).
  `kummer_logs.jl`.
  * Scope: one component θ = yᵖ, y = b^(1/q).
  * Residues over a pole form one orbit r·μ_q, with s = rᵠ ≡ hᵠbᵖ mod F; at ∞ likewise when q | m.
  * Supported: all s rational and in one class tᵠσ (σ q-th-power free), all t of one sign.
    L = ℚ(σ^(1/q)) (the factor of zᵠ − σ at the real root when reducible, e.g. 4^(1/4) = √2).
  * Look for v ∈ L[x, y] vanishing to order N·n at the branch-0 place of each pole: y ≡ S_F mod F, with
    the q-th root Hensel-lifted. At ∞:
    * n∞ = 0: q deg c_k + km ≤ Z with gcd(m, q) | Z (∞ may be ramified; this was a bug that the scan
      exposed).
    * n∞ ≠ 0: Puiseux conditions at the unramified places.
  * Riemann–Roch gives dimension ≤ 1. The yᵖ-component of λ v′/v (solved in L(x)[y]/(yᵠ − b)) is
    subtracted, and the rest must reduce to 0 by phase 3a. That is the exact verification.
  * Output: the log part is (λ/q)Σᵢ ζ^(−ip) log(τⁱv), written as a RootSum.
    * zᵠ − σ irreducible: (b₀/N)·RootSum over zᵠ = σ of z log v(z, x, y). z ↦ ζᶜz permutes the places
      like τ does; this also covers negative σ for even q, e.g. α⁴ + 1.
    * Otherwise: over αᵠ = 1.
  * Decisions for a prime index q ≥ 3 (2026-10-21, `kum_lp_order`):
    * L = ℚ(σ^(1/q)) doesn't contain ζ. The nontrivial isotypic parts of [Δ] are conjugate, and the
      trivial part comes from ℙ¹. So [Δ] is torsion iff its χ-part is, iff the integral is elementary.
      Composite q (4, 6) is not decided: an order-2 or order-3 part may be non-torsion without mattering.
    * No #J(𝔽_p) is needed:
      1. Find the order N₁ of Δ̄ at one good prime (p ≥ 7, p ∤ qσ, b and the poles squarefree and
         coprime mod p, a root of the minimal polynomial of σ^(1/q) mod p), by the same linear system
         over 𝔽_p, N ≤ 40.
      2. Test N₁Δ̄ at further primes. "Not principal" means infinite order: `NotElementary`.
      3. Otherwise run one exact test at N₁ over L. If it is principal, that gives the answer even
         when N₁ > Nmax; if not, `NotElementary`.
    * `kum_lp_data` and `kum_lp_system` are generic over L and 𝔽_p (`ModP` got `^`; its absence
      would have crashed the ∞ case).
    * Consistency test: with the search over L switched off (Nmax = 0), known torsion cases (orders 3,
      3, 5, 7) are still found from the order mod p and never declared non-elementary.
  * Chebyshev sweep: 504/504 decided (157/157 elementary integrated, 347/347 non-elementary proved).
  * Rubi scan: 46 OK, 1 NotElementary (consistent), 1 RischNotImplemented (a nested radical).
  * Decisions for composite q (2026-10-21, `kum_lp_order_T`):
    * Only the parts of [Δ] with characters of exact order q matter. T = Π_{ℓ|q}(1 − τ^(q/ℓ)) kills the
      others and not these (χ(T) ≠ 0). When L ∩ ℚ(ζ_q) = ℚ (`kum_cyclo_disjoint`: q odd, or σ > 0 and
      ℚ(√σ) ⊄ ℚ(ζ_q) by its conductor), the order-q parts are conjugate. So the integral is elementary
      iff T·[Δ] is torsion.
    * T·Δ lives on the branches y ≡ ζᵏS, so its orders are computed only mod primes p ≡ 1 mod q, by
      a per-branch system made effective with full fibers (`kum_branch_system`, with per-branch pole
      orders at ∞).
    * Different orders give `NotElementary`.
    * Construction over L, no ζ needed (2026-10-21):
      * Use the Galois trace T_G = Σ_{a∈(ℤ/q)*} T(τ^a) (`kum_TG`). It is invariant under τ ↦ τ^a, so
        T_G·Δ is defined over L. It still kills the lower-order parts and acts on the order-q parts by
        Θ = Σ_k c_k μ(q/gcd(k,q)) ∈ ℚ (= q in all cases tried).
      * Every level set of branches is a union of Galois orbits, so the conditions are rational
        (`kum_orbit_system`):
        * at the poles, v ≡ 0 mod (F^e, Q_J(y)) with Q_J = Π Y^φ(d) Φ_d(y/Y);
        * at ∞, Ramanujan-sum combinations Σ_k c_d(k − k₀) E_k(t) = 0.
      * λ = q b₀ σ^(1/q)/(N Θ). The rest is as for prime q (the yᵖ-part of λ v′/v, the exact check by
        phase 3a, RootSum output).
    * Decision: decide with T mod p (small multiplicities). If T·Δ has order N_T, the order of T_G·Δ
      divides N_T, so exact tests at the divisors of N_T either construct the answer or prove
      `NotElementary`.
    * Consistency test: with Nmax = 0, the torsion cases for q = 4, 6 (incl. (3+4x⁴)^(1/4)/x²) are
      constructed through T_G, and the rest reduces exactly.
    * Undecided: high genus where the orders mod small primes exceed the cap (40), e.g.
      1/((x−1)(x⁵+2)^(1/4)) (genus 6); negative σ for even q.
  * Several residue classes and mixed signs (2026-10-21):
    * Group the residues by class σᵢ (`kum_log_part`), and handle each class in `kum_log_class`.
    * Independence: when no σᵢ/σⱼ is a q-th power in ℚ(ζ_q) (checked with `kum_cyclo_disjoint` on
      the ratio), the spans σᵢ^(1/q)ℚ(ζ_q) are independent (Kummer). Then the integral is elementary
      iff each class divisor is torsion, and the log parts add up. Otherwise `RischNotImplemented`,
      e.g. classes −1 and 8 for q = 4, since (−4)^(1/4) ∈ ℚ(i).
    * Residues of both signs in a class: negative coefficients are made effective by full fibers. The
      plain Δ system is now the orbit system with T = 1 (level set "all branches but 0").
  * Several radicands in one component (2026-10-21):
    * θ = Π bₖ^rₖ, q = lcm of the denominators, θ^q = B = Π bₖ^(q rₖ) (singular when q rₖ > 1).
    * Use the integral basis ωⱼ = Π bₖ^{j rₖ} = θʲ/gⱼ (`KumCurve`). It is diagonal for τ (ωⱼ ↦ ζʲωⱼ),
      and θ = ω₁.
    * The rewrite: products ωᵢωⱼ = carry·ω_{i+j}; values θʲ/gⱼ at the poles (gⱼ a unit); at ∞
      ωⱼ ~ wʲ/Π lcₖ^⌊j rₖ⌋·x^ρⱼ·Π series; residues s = hᵠB; degree bounds q(deg cⱼ + ρⱼ) ≤ Z (ramified)
      or deg cⱼ ≤ o − ρⱼ.
    * One base is the special case ωⱼ = y^(jp mod q); the old (b, p, q) entry remains as a wrapper.
    * Good reduction mod p now also requires the bases to be pairwise coprime (`kum_good_mod`).
    * Consistency test: genus-0 components (every degree-0 divisor principal) with the search over L
      off are constructed by the decision path, for q = 3 (prime) and q = 4 (T_G).
  * Real forms (2026-10-21, `kum_real_logs`). The phase-3b RootSums Σ_r r log v(r) over rᵠ = σ
    (or αᵠ = 1, times σ^(1/q)) become explicit real logs and atans:
    * a real root r gives (r/2) log(v(r)²);
    * a conjugate pair r = μe^(±iθ) gives μ cos θ log(Re² + Im²) − 2μ sin θ atan(Im/Re).
    * cos and sin are square-root constants for angle denominators dividing 12 or equal to 8, i.e.
      q = 3, 4, 6 (and 8, 12 for negative σ). Otherwise (q = 5, 7, …) the RootSum stays.
    * A common √3 or √2 in the sines is factored out of Im (Im² gets a rational coefficient).
    * Checked numerically (Chebyshev sweep: all elementary log parts, now in real form). Answers are
      real-valued at real points.
* Next / not yet:
  * Nested radicals; phase 5 (radicals over exp/log).
* Gaps seen in Rubi's library:
  * Nested radicals.
  * Cube and fourth roots of radicands with three or more distinct factors (phase 3).
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

## Nested radicals (begun 2026-10-21)

1. Denesting (step DN): done, tests green (2026-10-21; `denest.jl`, a rewrite before the radical paths). √(a + b√c) with a, b, c ∈ ℚ(x) and a² − b²c = d² a square in ℚ(x):
   √(a + b√c) = √((a+d)/2) + s√((a−d)/2), where s = sign b on the interval used. (√p₁ + s√p₂)² =
   p₁ + p₂ + 2s√(p₁p₂) = a + s|b|√c. The integrand is rewritten and integrated with ordinary radicals.
   The answer is valid on the interval around a sample point where b keeps its sign.
   E.g. √(x + √(x²−1)), √(x + 2√(x−1)).
2. Done for u₁² of degree ≤ 2 with ℚ(i) residues, tests green (2026-10-21; `nested.jl`). The pieces
   are f₀ + f₁√c + 2 Re ∫ g u₁ with g = (f₂ + a f₃/b)/2 − i s f₃/(2b). The u₁ part is an Euler
   substitution over ℚ(i) and a rational integral over ℚ(i) (verified exactly by `derivative_of`).
   t is written back as an element τ of ℚ(i)(x)⟨1, y₁, y₂, y₁y₂⟩, and the real parts are exact (log|W|²,
   atan(W_im/W_re)). Rubi's problem works. Not yet: residues outside ℚ(i) (e.g. ∫√(√(1+x⁴) − x²)),
   u₁² of higher degree, e = +s² or e = s²c (cyclic).
   Original note: not denestable (e.g. Rubi's 1/((1+x⁴)√(√(1+x⁴) − x²)), where a² − c = −1). y₂ = √(y₁ − x²) and
   y₂·y₂′ = √(x⁴ − y₁²) = i, so ℚ(i)(x, y₂) is Galois over ℚ(i)(x) with group V₄. The projections live in
   ℚ(i)(x)(y₁), ℚ(i)(x)(y₂ + i/y₂), ℚ(i)(x)(y₂ − i/y₂), and (y₂ ± i/y₂)² = ±2i − 2x² (genus 0). This
   needs radicands with constants in ℚ(i) (Euler substitutions over ℚ(i)), then real forms.
3. General nested radicals: a primitive element and its minimal polynomial, i.e. phase 4.

## Phase 6: non-elementary answers with hypergeometric / elliptic functions

When an integral is proved non-elementary (phases 1, 3a, 2/3b decisions), the residue-free remainder
∫ (P/A)·θ dx is known exactly after Hermite reduction and the log part. Express it with special functions
(HypergeometricFunctions.jl, `_₂F₁`), as Rubi does, instead of raising `NotElementary`. The algebraic and
log parts stay elementary.

* H1: done, tests green (2026-10-21; `hypergeometric.jl`). `HypTerm`s are kept in an
  `IntegralWithRootSums` and evaluated numerically, so no symbolic package needs to know ₂F₁. They are
  hooked where phase 1 (hyperelliptic, not in step SQ mode) and phase 3a (Kummer, one binomial base) would
  raise `NotElementary` on a residue-free remainder. `HYP_ANSWERS[]` (default true; the decision tests
  set it false). Chebyshev sweep with it on: all 504 integrals answered and verified numerically (347 with
  ₂F₁). α < 0 is still `NotElementary`: the argument would cross the branch cut.
  Original plan: binomial radicands θ = (α + βxⁿ)ᵖ (one base, b = α + βxⁿ). The remainder is Σₖ cₖ xᵏ (α + βxⁿ)^(p−1)
  (P/A·θ with A = b). Each monomial:
      ∫ xᵐ(α + βxⁿ)^q dx = xᵐ⁺¹ (α + βxⁿ)^q / ((m+1)(1 + βxⁿ/α)^q) · ₂F₁(−q, (m+1)/n; (m+1)/n + 1; −βxⁿ/α)
  (m ≠ −1). The factor (α + βxⁿ)^q/(1 + βxⁿ/α)^q keeps the principal branch. Covers the Chebyshev
  sweep's 347 non-elementary cases and Rubi's elliptic-type answers in binomial form.
  * Output: a `_₂F₁` operation (OPS entry, deferred/placeholder call for symbolic packages without it,
    as for the SpecialFunctions answers); a dependency on HypergeometricFunctions.jl.
  * Verification: the derivative identity above is standard (as for Ei, erf answers); tests check
    numerically against the integrand.
  * Keep `NotElementary` available (e.g. a keyword or a flag on the result) so the decision is not lost.
* H3, incomplete gamma: done, tests green (2026-10-21; `gamma_terms.jl`).
  * ∫ xˢ e^(bx+d) dx = −e^d (−b)^(−s−1) Γ(s+1, −bx) for b < 0, s ∉ ℤ (rational, or a symbolic exponent such
    as t^(a−1)e^(−t)). Integer-s terms of the sum go to the usual integrator; half-integers already give erf.
  * Tried as a fallback when the integral is decided `NotElementary` (with `HYP_ANSWERS[]`).
  * The Γ term is a symbolic `gamma(s+1, −bx)` when the term type can build one (Expr), else a `GammaTerm`
    evaluated numerically (numeric s).
  * Not yet:
    * a symbolic exponent with SimpleExpressions / SymEngine (neither represents gamma(a, x));
    * b > 0 (Γ at a negative argument);
    * other shapes, e.g. P(x)·xˢ e^(bx) with P a polynomial: it works term by term only if written as a sum.
* H2, general remainders on hyperelliptic curves of genus 1: reduce to Legendre/Carlson forms (F, E, Π)
  through the roots of a (needs algebraic numbers), or Appell-type functions. Larger.
* H4, exponential/trigonometric integrals beyond the Risch Ei/Si/Ci answers (requested 2026-10-21): planned.
  * Generalised exponential integral: ∫ xˢ e^(bx) for b > 0 and the E_n family (`expint(n, z)` in
    SpecialFunctions), e.g. ∫ e^(−x)/xⁿ = −E_n(x) x^(1−n)… relations with Γ(1−n, x); ∫ e^(bx)/xⁿ for symbolic n.
  * Sine/cosine integrals with powers and shifts: ∫ sin(ax + c)/xⁿ, ∫ cos(ax²)/x, ∫ sin(x)/(x + a),
    ∫ xˢ sin(bx) via Γ(s+1, ±ibx) (real and imaginary parts), sinh/cosh analogues (Shi, Chi).
  * As H3: tried after a `NotElementary` decision, symbolic `expint`/`sinint`/`cosint` when the term type
    has them, else numeric terms (the special-function fallback below).
* Special-function fallback (done 2026-10-21, `special_fallback.jl`): term types without expinti, li2, Si,
  … methods (SymEngine, Giac terms) integrate through Expr; the special-function terms become `ExprTerm`s,
  evaluated numerically in an `IntegralWithRootSums`. Apostol 156–174 for SymEngine and Giac.

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
