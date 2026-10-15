# Refactor plan: a general constant field under the Risch tower

Read this file, then `Risch.jl` (≈3167 lines; its module docstring has the stage roadmap).
Attach to the new session: `Risch.jl`, this file, and the five test files `test_risch.jl`,
`test_tower.jl`, `test_integrate.jl`, `test_trig.jl`, `test_constants.jl`. (`RISCH_STATUS.md` was lost; its essentials —
ground rules, lessons learned — are kept in §0 and §4 here. `Gruntz.jl` is a finished, separate project.)

## Progress

* Step 1 (baseline): done. Step 2 (alias `C`): done.
* Step 3 (constant field as a type parameter): done, tests green (2026-10-13). Everything below
  the front end is generic in `C`; still ℚ-only *by design*: Stage 5a quadratic residues (`QuadLog`,
  `QuadAtan`, `quad_terms`, the `C === Q` branch of `log_part` → step 5), the legacy `parse_rational`,
  Stage 5c (`QI`/`EP`, → step 7), and leaf parsing (`lq(T, r, 0)` embeds ℚ).
* Step 4 (`is_constant`): done, tests green (2026-10-13). `is_constant(T, f)` and
  `dconst_value(T, f)` (value in C of a differential constant, `nothing` otherwise) are used in
  `make_exp`/`make_log` (constant argument, constant ratio), `rde` (cancellation exponent `i0`) and
  `residue_logs` (residue criterion). Structural test first, then `D f == 0`; a differential constant
  outside C raises `RischError` (invalid tower). `const_value` stays only for the constant exponent in
  `parse_tower` (a rational-number role).
* Step 5, part 1: done, tests green (2026-10-13). New, not yet used by
  `risch_integrate`:
  * `QS{d}` (ℚ(√d)) implements the constant-field interface: `cfromQ`, `crational`, `cflat_all`,
    `constant_roots` (rational roots, then the quadratic formula via `qs_sqrt` once ≤ 2 roots remain),
    `cterm` (`a + b·sqrt(d)`, `sqrt(d)` symbolic), plus `^`, `hash`, `show`.
  * `constant_roots` contract made explicit: the result may be incomplete; callers treat a leftover
    factor as not handled (true for `log_part` and `residue_logs`).
  * `change_constants(T, C′, φ)` rebuilds a tower over C′ for a field embedding φ;
    `change_constants(T, T′, f, φ)` maps an element. φ commutes with D (tested).
  * New test file `test_constants.jl`: ℚ(√2) arithmetic and roots, D ∘ φ = φ ∘ D on towers, towers built
    directly over ℚ(√2) equal the mapped ones, integration over ℚ(√2) towers verified exactly, and
    ∫1/(x²-2) with residues ±√2/4 output with a symbolic sqrt(2).
* Step 5, part 2: done, tests green (2026-10-13). In `residue_logs`, a leftover irreducible
  quadratic residue factor over ℚ (roots α ± β√d) is handled by `tower_quad_terms`: map to the tower
  over ℚ(√d) with `change_constants`, `W = gcd(D, A - a·δD)` there, split `W = U + √d V` with the
  conjugation σ (U, V are σ-invariant, read back exactly), and return `α log(U² - dV²)` plus a
  `TowerQuadLog` (d > 0) or `TowerQuadAtan` (d < 0). `ElemIntegral` has a `quads` field; Stage 5a terms
  from the base level are carried into towers (`tower_quad`) instead of raising. Exp correction: the
  α-log counts as `α·deg(U² - dV²) = 2α·deg W`, exactly the two conjugate logs; the ratio term adds none.
  Still `RischNotImplemented`: residue factors of degree > 2 (e.g. `1/(x(log⁴x + 1))`), quadratic pairs
  over a constant field other than ℚ, and atan/quadratic terms multiplying a power of a log
  (`log(x)/(x²+2)`). `test_integrate.jl`: new testset of 10 integrands; `atan(log x)` and `atan(exp x)`
  moved there from "awaiting later stages".
* Step 6, part 1: done, tests green (2026-10-13). Not yet used by `risch_integrate`:
  * `cfield(k)` = ℚ(t₁, …, tₖ) as nested `Frac{UPoly{…}}` over ℚ; `tgen(C, j)` is tⱼ; `cdepth`.
    Interface: `cfromQ`, `crational` (unique normal form ⇒ rational iff constant at every depth),
    `cflat_all` (clear the common denominator, flatten numerator coefficients), `constant_roots`
    (rational roots via ℚ-coordinate polynomials, then quadratic formula with `csqrt`), `cterm`.
  * `csqrt` for ℚ, ℚ(√d), ℚ(t…); `psqrt` (verified polynomial square root).
  * `ConstGen(kind, arg)` (tⱼ = exp(arg) or log(arg), arg ∈ ℚ): the meaning of the generators,
    kept in `T.consts` (copied by `change_constants`) and `Builder.consts` (4th field; the
    3-argument constructor is kept). `cterm` builds `exp(1)`, `log(2)`, … through `mk` (deferred).
  * Independence of the tⱼ is an assumption (Schanuel) once there are two or more; exact for one.
  * Bug fixed for C ≠ ℚ: in `integrate_log_poly` the log coefficient c of `∫ lc(p) = v + c·log u` was
    solved over ℚ (`solve_relation`); it must be a constant of C (`c = tgt/(u'/u)`, D c = 0), e.g.
    `∫ e·log(x)/x`. Identical for C = ℚ.
  * `test_constants.jl`: ℚ(t) arithmetic/relations/roots/sqrt, rational integrals over ℚ(t)(x)
    (residues ±1/(2e), (1 ± e)/2), towers over ℚ(t) (Risch DE, residues, log polynomial with c = e),
    output with `exp(1)` / `log(2)` checked numerically in both packages.
* Step 6, part 2: done, tests green (2026-10-13).
  * Generators (`T.consts`): at most one exp constant tₑ = exp(1/s), kept FIRST (innermost), refined like
    exp generators (`exp(1)` then `exp(1/2)` → tₑ = e^(1/2)); one `log p` per prime p. `const_exp(T, c)`
    handles c = a + Σ r_p log p (a ∈ ℚ, r_p ∈ ℤ); `const_log(T, c)` handles c = r·tₑ^m (r ∈ ℚ₊, m ∈ ℤ).
    A missing generator throws `NewConstants`; `build_tower` re-parses over `cfield(k)` (≤ `MAX_CONSTS` = 8).
    `build_tower(f, xk; constants = nothing)`: automatic; an explicit field forbids new constants.
  * `make_exp` now uses the structure theorem through derivatives (u' = Σ ρᵢ bᵢ' over ℚ, offset
    u − Σ ρᵢ bᵢ ∈ C → `const_exp`); equivalent to the old ℚ-relation test when C = ℚ. `make_log` passes
    a constant ratio ≠ ±1 to `const_log` (ratio −1 still dropped as before: log(−1) = iπ).
  * Leaves `E`/`ℯ`/`exp(1)` → tₑ^s. `risch_integrate`/`tower_derivative` pass `T.consts` to the Builder.
  * Tests: `test_tower.jl` (new "transcendental constants" testset; `exp(x)+exp(x+1)` and
    `log(x)+log(2x)` moved out of "rejected"), `test_integrate.jl` (12 integrands + one NotElementary).
  * Not covered: `sin(x+1)` (trig path, step 7); exp of non-integer multiples of log p, exp(e), log(e+1)
    (`RischNotImplemented`). SimpleExpressions evaluates constant-only calls eagerly, so `exp(1)` and
    `log(2)` written alone arrive as Float64 and are rationalized (pre-existing float behaviour); inside
    an expression in x (`exp(x+1)`, `log(2x)`, `2^x`) they work in both packages.
* Step 7 is split in three parts:
  1. done, tests green (2026-10-13): field machinery, no behaviour change.
     * `QS{D}` is now an alias of `QSB{D,Q}`; `QSB{D,B}` = B(√D) over a base field B (ℚ or ℚ(i)),
       arithmetic and interface generic in B (`qs_sqrt` via `csqrt` of B; identical results for B = ℚ).
     * ℚ(i) (`QI`) implements the interface: `cfromQ`, `crational`, `cflat_all` ([re, im]), `qi_sqrt`,
       `constant_roots`; plus `^`, `show`, `zero/one` on instances.
     * One root finder for all non-ℚ fields: `constant_roots_generic` (rational roots through the
       ℚ-coordinate polynomials, then the quadratic formula with `csqrt`); the ℚ(√d) and ℚ(t…) copies
       are replaced by it (same algorithm).
     * `cconj`: complex conjugation on constants (ℚ(i), B(√d) with d > 0, or ℚ(√d) with d < 0 where
       √d ↦ −√d, and ℚ(i)(t…) coefficientwise with the tⱼ real).
     * `cfield(k, base)`: ℚ(i)(t₁, …, tₖ) with `base = QI`; `cbase(C)`.
     * Tests (`test_constants.jl`): ℚ(i), ℚ(i)(√3), ℚ(i)(t) arithmetic/roots/sqrt/conjugation;
       rational integrals over ℚ(i); a hand-built exp(ix) tower over ℚ(i) (Risch DE, residue i,
       Laurent terms) verified exactly.
  2. done, tests green (2026-10-13): trig in the main tower, real-form output.
     * `parse_tower`: sin/cos/tan of any tower element via θ = exp(i·u); `NeedComplex` makes
       `build_tower` re-parse over base ℚ(i) (`cfield(k, QI)`); atan/abs still refused.
     * `risch_integrate`: Stage 5c (polynomial × exp × trig) first; on `RischNotImplemented` the ℚ(i)
       tower, `integrate_el`, exact `check_tower`, then `to_term_real`.
     * Real form (`sigma_kinds`, `tconj`, `real_term`, `real_log_pieces`, `to_term_real`): σ = complex
       conjugation on the tower (generators :real or :trig, σθ = 1/θ); v ↦ (v + σv)/2 written with
       cos(kw), sin(kw) via (N·σD)/(D·σD); c log w ↦ c_r/2 log(wσw) − c_i atan(V/U) (c_r log w if w
       real). The real form is re-verified exactly (D(real form) == f) before output.
     * Quadratic residue pairs over ℚ(i): `qi_split_sqrt` (Δ = s²d, d > 1), `ExtQuadPair` over the tower
       mapped to ℚ(i)(√d) (`QSB{d,QI}`), exp correction 2α·deg W, checked in `check_tower`.
     * `cterm` for real-valued ℚ(i) / ℚ(i)(√d) constants; `tower_derivative` outputs real form.
     * `const_exp`/`const_log` accept plain ℚ(i) (e.g. sin(x) + log(x) + log(2x) → ℚ(i)(log 2)).
     * Tests: `test_trig.jl` (13 new integrands incl. 1/(2+cos x), tan, sec, sin(x+1); Si, Ci, Fresnel now
       decided `NotElementary`), `test_tower.jl` (trig towers and derivatives).
  3. done, tests green (2026-10-13): the constant τ = e^(i·a).
     * `ConstGen(:expi, a)`: τ = e^(i·a), at most one, refined like the exp constant, placed right after
       it. `const_exp` splits c = a + b·i + Σ r_p log p (the i column only over ℚ(i)); `const_gen_power`
       adds/refines generators. Constants with denominators > `MAX_CONST_DEN` (1000) are refused
       (rationalized floats, e.g. SimpleExpressions' log(2)).
     * `cconj_g(gens, c)`: conjugation knowing the generators (σ fixes e^a and log p, σ τ = 1/τ); used
       by `tconj` at level 0 and by `real_log_pieces` (zero is returned unchanged: the
       reversal uses τ^deg, and deg 0 = -1).
     * Output: `cterm` of a real constant in B(τ) via (N·σD)/(D·σD) Laurent form with cos(k·a), sin(k·a)
       (`cterm_expi`, `cterm_laurent`). So cos(1), sin(1) are now usable constants (SymEngine keeps them).
     * Tests: `test_trig.jl` (sin(x)+sin(x+1), sin(x)cos(x+1), cos(x+1/2)+sin(x), exp(x+1)sin(x)+sin(x+1),
       x cos(1) + sin(x)); `test_tower.jl` (constants {e^i}, refinement to e^(i/2), {e, e^i}; derivatives).
       Refused: sin(x) + sin(x + log 2) (2^i).
* Step 8 (user's choice: special-function answers ON by default; `SpecialFunctions` is loaded by the
  module like TermInterface: `using SpecialFunctions: expinti, sinint, cosint, erf, erfi`).
  * 8a: done, tests green (2026-10-13). Where the algorithm proves ∫ a θ^j non-elementary
    (θ = exp(U)), `special_exp` solves the parametric RDE  a = y' + jU'y + Σ_t c_t U'/(U−t) [+ k]
    (`rde_param_base`, base level): Ei terms c·e^(jt)·Ei(j(U−t)) with shifts t = U(poles of a) and 0;
    erf/erfi for jU = Ax² + Bx + C₀ (A ∈ ℚ). Above the base level only a = c·U'/U → c·Ei(jU)
    (∫ exp(exp x) = Ei(eˣ)). At a log level with non-constant residues and denominator θ + b (b ∈ C),
    `special_log`: ∫ c'uᵐu'/(θ+b) = c'e^(−kb) Ei(k(θ+b)), k = m+1 (li(x) = Ei(log x), x/log x).
    `SpecialTerm` keeps the exact derivative (→ `check_tower`, real-form check). Output: Ei, erf, erfi;
    over ℚ(i) the real part, Ei(iw) → Ci(w) + i·Si(w) (sign of w normalised; e^(jt) coefficients as
    e^pr(cos ps, sin ps)). Columns with no real form (complex Ei, Fresnel) are not offered, so those
    stay `NotElementary`. Still `NotElementary`: dilog, x^x, 1/(x + log x), ∫ x·exp(x + eˣ),
    eˣ sin(x)/x, sin(x²). No li/Fresnel/polylog in SpecialFunctions.
    SymEngine: `expinti(::Basic)` etc. are not defined, so its special-function tests are skipped
    (`@test_skip`) until the package side provides them.
  * 8b: done, tests green (2026-10-13). Audit of every `NotElementary` source:
    rde_base (f = j·u' has no simple poles: bounds complete), log-case RDE (deg y ≤ deg g, or
    = deg g − deg f; no normal poles possible), decoupled exp case (exp(−j u) t^(−i) ∉ k, so
    coefficients outside supp g vanish), residue criterion (normal denominators), limited
    integration in `integrate_log_poly`: sound. The gap was the cancellation exponent in the exp
    branches (only constant homogeneous solutions were found). `cancellation_exponent` now finds
    s with f₀ + s w' a logarithmic derivative in k: f₀ = Σ ρᵢ (generator log-derivatives, δq/q for
    normal squarefree factors of the denominators, split by rational roots at the base) − s w' over ℚ;
    s is unique (w' ∉ span); integrality decides; a possibly too-coarse factor list gives :unknown,
    and then a failed search raises `RischNotImplemented` instead of `NotElementary`.
    Regression tests: ∫ exp(x + log x + eˣ)/x and ∫ exp(2x + log x + eˣ)e^(−x)/x = exp(eˣ) (were wrong
    `NotElementary`). Still `RischNotImplemented` (honest): normal denominators in tower RDEs (needs
    Bronstein 6.1–6.4: weak normalization, normal/special denominators, SPDE), simple poles of f.
* **Step 9 — the full Risch DE in towers** (outline in §3, step 9).
  * 9a: done, tests green (2026-10-13). `rde` dispatches to `rde_general` when f or g is not
    Laurent-shaped (normal denominators). Pieces: `split_factor`, normal denominator (h = gcd(e,∂e)/
    gcd(p,∂p); c with a normal denominator left ⇒ no solution), special denominator for exp (lowest
    power of t via `cancellation_exponent` when ν(b) = 0), degree bounds (primitive and exp cases;
    cancellation sub-cases checked with `limited_log_multiple` / `logderiv_status` / 8b), `spde`,
    `poly_rde_reduced` (deg b̄ > 0 top-down; b̄ ∈ k* decoupled (exp) or triangular (log); b̄ = 0
    integration without logs). Weak normalisation is not implemented: f with simple normal poles
    raises `RischNotImplemented` (f = j u' never has them). Undecidable cancellation ⇒
    `RischNotImplemented`, never a wrong "no solution". Candidate verified exactly.
    Tests (`test_integrate.jl`): exp(eˣ)e^{2x}/(eˣ+1)², exp(eˣ)eˣ(1/(eˣ+2) − 1/(eˣ+2)²),
    (1/(log x + 1) − 1/(x(log x + 1)²))eˣ, exp(sin x)(cos x/(2+cos x) + sin x/(2+cos x)²);
    decided: exp(eˣ)/(eˣ+1).
  * 9b: done, tests green (2026-10-13). (Pieces 4–5 went into 9a; 9b solves the
    primitive cancellation cases.) `logderiv_solve(T, km, h)` returns (:yes, z) with z'/z = h
    (z built from the relation and verified), :no or :unknown; `logderiv_shape_ok` is a cheap
    necessary condition (top-level polynomial part of degree ≤ 0, no θ^-v at exp levels) that turns
    many :unknown into :no (also used in `cancellation_exponent`). Primitive cancellation
    (`prim_cancel`): b = z'/z ⇒ (z h)' = z c, h = (∫ z c)/z with `integrate_poly_t` (only κ·log u = κ t
    allowed as a new log); used in the Laurent log branch (before the triangular solve, which also
    avoids `rde_base`'s simple-pole refusal) and in `poly_rde_reduced`. Degree bound, log case
    deg b = deg a with −lc(b)/lc(a) = z'/z: β = −[t^(da−1)](a z' + b z)/(z lc(a)); β = m t' + w' ⇒
    n = max(n, m) (`limited_log_multiple`). Tests: direct `Risch.rde` calls on t = log x with f = ±1/x.
  * 9c: done, tests green (2026-10-13).
    * Weak normalisation (Bronstein 6.1) at every level, including the base: `weak_normalizer`
      (simple-pole part d1, residue resultant `residue_poly`, positive integer roots through the
      ℚ-coordinates `positive_integer_roots`, q = Π gcd(a − n Dd1, d1)ⁿ); `rde_general` starts with
      y = z/q, z' + (f − Dq/q) z = g q. The old refusal for simple normal poles is gone.
    * Base level in `rde_general` (t = x primitive over C: `polyD`, `coeff_type`, base cases in
      `logderiv_solve`, `limited_log_multiple`, `poly_rde_reduced`). `rde_base` returns `:general`
      instead of refusing (simple poles of f, also where g is regular: its bound missed poles of y at
      positive integer residues of f; and the simple pole at infinity); `rde` then calls
      `rde_general(T, 0, …)`.
    * Log level b = 0 in `poly_rde_reduced` allows κ·t (`integrate_poly_t`).
    * Factor lists: `normal_factors!` splits the top-level simple-pole factors by residue
      (Rothstein–Trager, `residue_split!`), base factors by rational roots (`linear_split!`), and
      reports `exact`; `factor_candidates` unlifts elements, includes the generators'
      log-derivatives (`gen_logderivs`) and refines (`refine_factors`). `cancellation_exponent` and
      `logderiv_solve` answer :unknown only when not exact.
    * Tests: base/log weak normalisation via direct `Risch.rde`; `logderiv_status` on
      p1'/p1 + 3 p2'/p2 (:yes) and p1'/p1 + ½ p2'/p2 (:no) with irreducible quadratics.
  * Remaining refusals: residues that are not constants in the RT split, nonlinear multiple factors,
    limited integration with atan/quadratic terms. Next (optional): 9d, parametric RDE in towers.
* Step 9d: done, tests green (2026-10-14). Parametric Risch DE in towers and limited integration.
  * `prde(T, m, f, G)`: a basis [(y, c)] of all solutions of y' + f y = Σ cᵢ gᵢ (c ∈ C^r), or
    `nothing` when not handled (undecided cancellation, weak normaliser residue > 1000). Steps of
    `rde_general` with every "Σ cᵢ (…) = 0" turned into a linear constraint over C (`cflat_c`
    = C-coordinates, `nullspace_cols`, `c_nullspace`) and re-parametrisation (`cback`):
    weak normalisation, normal denominator, normal-pole constraint, special denominator,
    `rde_degree_bound` (factored out of `rde_general`, shared), `prde_spde` (parametric SPDE),
    `prde_poly` (deg b̄ > 0 top-down, linear in the right sides; b̄ ∈ k coefficient by coefficient,
    each a recursive `prde` in k whose parameters are the current basis — covers integration and
    the cancellation cases without a log-derivative test). Every basis element verified exactly.
  * `special_exp` uses `prde` at every level (`rde_param_base` removed): Ei terms with shifts t
    (constant roots of res_θ(normal part of den α, U.num − z U.den) above the base) and new
    Ei(j(U − a_l)) terms for exp generators θ_l = exp(a_l) below (extra θ_l^(−j) W'/W). Over ℚ(i)
    above the base, arguments are filtered with `tconj` (real or i·real). New answers:
    exp(eˣ)/(eˣ+1) = Ei(eˣ) − e⁻¹Ei(eˣ+1), x·exp(x+eˣ) = x exp(eˣ) − Ei(eˣ), eˣ log x in either
    tower order, e^(2x) log x.
  * Limited integration decided: in `integrate_log_poly`, `integrate_poly_t`, `limited_log_multiple`
    an atan / quadratic / ExtQuadPair / SpecialTerm in ∫ lc means residues outside C (or ∫ lc not
    elementary), so lc ≠ b' + c t': `NotElementary` / `nothing` instead of a refusal.
    log(x)/(x²+2), log(x)/(x²+1), log²(x)/(x²−2) are now decided `NotElementary`.
  * Tests (`test_integrate.jl`): new testset "parametric Risch DE in towers (step 9d)" (exact
    `prde` bases at base / log / exp levels; 5 Ei integrands; x·exp(eˣ), exp(eˣ)/x still decided).
* **Step 10 — radicals by substitution** (outline in §3, step 10).
  * 10a: done, tests green (2026-10-13). One linear-fractional radicand u = (ax+b)/(cx+d)
    for all radicals (sqrt, cbrt, u^(p/q)); n = lcm of the indices; t = u^(1/n), x = φ(t) =
    (b − d tⁿ)/(c tⁿ − a). `collect_radicals` / `radical_parts` find them, `radicand_element` parses
    the radicand (must be in ℚ(x)); a parse hook `T.subst` (new Tower field; `build_tower(…; subst)`)
    maps x ↦ φ(t) and u^(p/q) ↦ t^(pn/q) while the integrand is parsed straight into a tower over ℚ(t)
    (so exp/log/trig of radicals work); the integrand f·φ'(t) is integrated and verified exactly with
    the shared core `integrate_built`; output uses a Builder whose variable is the term sqrt(u) /
    u^(1/n). Refused: several radicands, degree ≥ 2 radicands (→ 10b), nested radicals, radicals of
    non-rational expressions. `risch_integrate` checks for radicals first.
  * 10b: done, tests green (2026-10-14). One quadratic polynomial radicand Q = Ax² + Bx + C
    with only half-integer powers: `euler_substitution` (√A rational: t = √Q + √A x; √C rational:
    t = (√Q − √C)/x; rational roots r₁ ≠ r₂: t = √Q/(x − r₁), r₁ the smaller root when A < 0) gives
    x = φ(t), √Q = ψ(t) rational over ℚ, exact identities for the principal root; the rest of the
    pipeline is shared with 10a (`integrate_radical` now takes φ and a radical-power map).
    Refused: Q needing ℚ(√d) (e.g. √(2 − x²)), other indices, quadratic denominators.
    Tests: asin/asinh/acosh-type integrands, √C and rational-root cases, exp(√(x²+1))·x/√(x²+1).
  * 10c: done, tests green (2026-10-14). √Q, Q quadratic, without a ℚ-rational Euler substitution.
    `euler_substitution` now returns candidates [(S, φ, ψ, t-term)], tried in order by
    `integrate_radical` (body moved to `integrate_subst`; the first handled one decides, a
    `NotElementary` from any is a proof): the 10b cases, then a small rational point (x₀, y₀) of
    R² = Q (height ≤ 12, `euler_point`: R = y₀ + t(x − x₀), S = ℚ), then over S = ℚ(i)(√d)
    (`QSB{d,QI}`, `qs_field`): √A (A > 0), the point (0, √C) (C > 0), the vertex (A < 0).
    i is in S for the atan terms; `is_complex_field` includes `QSB{d,QI}` (real-form output, and
    trig parsing over it). Real form: `merge_pieces` combines conjugate atan/log pieces
    (atan(−u) = −atan(u)); at the base atan(V/U) with V constant becomes −atan(U/V) (no pole at U = 0,
    e.g. 2 atan((√(3−x²) − √3)/x)). New: 1/√(2−x²), √(3−x²), 1/√(4x−x²−1), 1/√(2x²+3),
    1/(x√(2x²+3)) (needs √3: second candidate), exp/sin of such radicals; decided
    exp(x)√(3−x²) `NotElementary`. Refused: never-positive radicands, answers needing two square
    roots (1/((x+1)√(3−x²)): √2 and √3).
  * 10d: done, tests green (2026-10-14). Two radicands, square roots of linear polynomials
    u₁ = a x + b, u₂ = c x + d (`integrate_two_radicals`): y = √u₁ gives x = (y² − b)/a and
    u₂ = (c/a) y² + d − c b/a, so √u₂ is the 10b/10c case in y (`euler_substitution` with the
    Builder variable √u₁); composed: x = (φ₂(t)² − b)/a, √u₁ = φ₂(t), √u₂ = ψ₂(t). Both orders are
    candidates. Refactor: radicals are grouped by radicand; `integrate_subst` takes
    `radval(u, e)` (u^e ∈ S(t)); `try_substitutions` is shared by 10c/10d.
    New: √x + √(x+1), √x √(x+1), 1/(√x + √(x+1)), 1/(√(x+1) − √(x−1)), √(2x+1)√(3x+2) (over ℚ(√6)),
    √x √(1−x), log(√x + √(x+1)), exp(√x + √(x+1))(…); decided exp(x)√x√(x+1) `NotElementary`.
    Refused: three or more radicands, other indices, higher-degree radicands (genus ≥ 1 in
    general, e.g. √x √(x²+1)), radicands never real together; constant radicals such as
    sqrt(2) in the integrand (SymEngine turns √x √(2x) into sqrt(2)·x).
  * 10e: done, tests green (2026-10-14). Square roots of rational constants in the integrand
    (sqrt(2), 2^(3/2), sqrt(8)): radicals whose radicand is a constant (`is_const_radicand`) are
    constants v^(p/2) = v^((p−1)/2)·σ√d (`const_radical_field`); all must share one squarefree d,
    and the tower is built over ℚ(i)(√d) (= `QSB{d,QI}`, as in 10c: atan, trig, real-form output).
    `try_substitutions` / `integrate_subst` take the context `cfix` (field, value function):
    substitutions over ℚ are embedded, over ℚ(i)(√d) kept, over another ℚ(i)(√d') skipped;
    `euler_substitution(…; pref = d)` first looks for a point (x₀, y₀) with y₀ ∈ ℚ√d
    (√2·√(3−x²) through (1, √2)). Only constant radicals: the identity substitution x = t.
    Tests SymEngine only (SimpleExpressions evaluates sqrt(2) eagerly to a Float64).
    Refused: √2 and √3 together, cube roots of constants, √ of negative constants,
    √6·√(3−x²) (needs √3 too), 1/(2 + cos(√2 x)) (quadratic residue pair over ℚ(i)(√2)).
    Note: special-function answers (Ei, erf, erfi) fail in SymEngine (`expinti(::Basic)` etc.
    undefined), e.g. ∫ exp(√2 x + x²), as already for ∫ exp(x²).
* **RootSum** (2026-10-14, done, tests green; user's choice: a Risch-owned struct). Residues of
  degree > 2 in ℚ(x) integrands (left by `log_part` as `unresolved`): for each factor Q(z),
  W = gcd(D, R − z D′) in (ℚ[z]/Q)[x] by dynamic evaluation (`d5_monic`, `d5_rem`, `d5_gcd`: a
  zero-divisor leading coefficient splits Q, so no factorisation and Q may be reducible), monic
  in x → `RootSum(poly, W, var)` = Σ_{Q(α)=0} α log W(α, x). Exact verification in ℚ(x)
  (`rootsum_derivative`): norm N = res_z(Q, W), cofactor N/W (division checked mod Q),
  derivative Tr(z·∂ₓW·N/W)/N with `power_sums` (Newton). `integrate_built` (base level, C = ℚ)
  returns `IntegralWithRootSums(elementary term, rootsums, var)`: printed as
  `elementary + RootSum(α -> α*log(x + (…α…)), α^3 - … = 0)`, callable `F(a)` = real part of the
  numeric value (`term_value` walks the package term via TermInterface; roots by Aberth,
  `numeric_roots`). Exported: `RootSum`, `IntegralWithRootSums`. Tests: `test_risch.jl`
  (exact testset incl. a d5 split; both packages numerically: 1/(x⁴+1), 1/(x³+x+1), 1/(x⁵+x+1), …).
  Not covered: RootSums inside towers (1/(x(log⁴x + 1)), still `RischNotImplemented`), over
  constant fields other than ℚ, a real form (atan/log pairs) of the RootSum; `integrate(F, y)`
  (iterated) on an `IntegralWithRootSums` is not supported.
* **Real form of RootSum**, in two steps (user's request after RootSum).
  * **R1** (2026-10-14, done, tests green): factor the residue polynomial over ℚ (`factor_Q`: big
    prime p > 2·|lc|·2ⁿ‖f‖₂, Cantor–Zassenhaus `fp_ddf`/`fp_edf` with a fixed LCG, Miller–Rabin
    `is_probable_prime`, subset recombination checked by exact division over ℤ). In `log_part`
    (C = ℚ) each quadratic factor goes through `quad_factor!` (the old degree-2 code, extracted:
    log + atan, or `quad_terms`); only the product of the other factors stays `unresolved`.
    E.g. 1/((x²+3)(x⁴+2)) → √3/33·atan(x/√3) + quartic RootSum; 1/(x⁵+1) → log + quartic RootSum.
    Tests: `factorisation over ℚ` testset, quadratic split-off in the RootSum testset.
  * **R2** (2026-10-14, done, tests green): real form for an irreducible quartic residue factor q
    whose roots u ± iv lie in ℚ(i, √d), d > 0 (`quartic_real!`, called from `log_part` after R1).
    `conj_pair_factors`: pair sums are the roots of S(t), S² = res_z(q(z), q(t−z)) / 16q(t/2);
    a linear (then p₁, p₂ from a quadratic over ℚ) or quadratic factor of S gives d and
    q₁ = z² − 2uz + u² + v² over ℚ(√d) (gcd(q(z), q(s−z)), checked to divide q); v = `qs_sqrt`
    (u² + v² − u²). Each pair: W = gcd(D, A − (u+iv)D′) over ℚ(i)(√d) = U + iV and, as in
    `quad_factor!`, u log(U²+V²) ± 2v atan(U/V or V/U). Both pairs go into one
    `RationalIntegral{QS{d}}` kept in `quads` (only their sum has a derivative in ℚ(x));
    `derivative_of` maps it back with `qs_down` (error if not in ℚ(x)), `to_term` prints it with
    sqrt(d). E.g. 1/(x⁴+1) → √2/8 log(x²+√2x+1) − √2/8 log(x²−√2x+1) + √2/4 atan(√2x+1) +
    √2/4 atan(√2x−1); also 1/(x⁴+9) (√6), 1/(x⁴−x²+1) (√3), 1/(x⁸−1), 1/(x⁶+1).
    Not covered (stay RootSum): roots needing other fields, e.g. 1/(x⁴+2) (2^(1/4)), 1/(x⁵+1)
    (Im ζ₅ = √(10+2√5)/4: nested), degree ≥ 6 factors (the octic of 1/(x¹²+1)); atan arguments
    are rational functions, not Rioboo's polynomial LogToAtan form.
    Tests: `real form of quartic RootSums (R2)` testset (exact), both packages numerically;
    `risch_sym_eval` drops roundoff imaginary parts of SymEngine's `N` (as `trig_sym_eval`).
  * **R3: atans of polynomials** (2026-10-14, done, tests green). `log_to_atan(A, B)` (Rioboo,
    Bronstein §2.8): polynomials pⱼ with Σ 2 atan(pⱼ) ≡ 2 atan(A/B), so the antiderivative has no
    ±π jumps at the real zeros of B. Used at the base level in `quad_factor!` (over ℚ),
    `quartic_real!` (over ℚ(√d)) and `quad_terms` for d < 0 (over ℚ(√e): A = U is even and
    B = √e V odd under √e ↦ −√e, so every pⱼ = √e uⱼ, uⱼ ∈ ℚ[x], and the output stays
    `QuadAtan(2β, e, uⱼ, false)`, which towers already lift). E.g. Bronstein's
    (x⁴−3x²+6)/(x⁶−5x⁴+5x²+4) → atan((x⁵−3x³+x)/2) + atan(x³) + atan(x) (was −atan((x²−2)/(x³−3x)),
    jumping by π at 0, ±√3). Not changed: tower levels (`TowerQuadAtan`, polynomials in θ) and the
    real-form output of Step 7.
    Fixed with it: (1) R2 terms reaching a tower (exp(x) + 1/(x⁴+1)) raised a MethodError in
    `tower_quad`; now `RischNotImplemented` (lifting R2 terms into towers is a possible next step).
    (2) `F(a)` of an `IntegralWithRootSums` from a radical substitution evaluated the RootSum at x
    instead of t (e.g. t = sqrt(1+x)): `RootSum` has a field `arg` (the term of its variable),
    `risch_integrate` sets `var` to the integration variable.
    Tests: `Rioboo's LogToAtan` testset (derivative identity, Bronstein's answer, polynomial
    arguments); both packages: continuity on [−3, 3], RootSums under substitutions, the refusal.
  * **T: real forms inside towers** (2026-10-14, done, tests green).
    * T1: an R2 result (RationalIntegral over ℚ(√d), x only) reaching a tower through
      `integrate_el(T, 0, …)` becomes `BaseTerms(q, deriv)`: exact derivative in ℚ(x) stored for
      `check_tower`, output by the base `to_term`; no θ, so no exp correction. E.g.
      exp(x) + 1/(x⁴+1), log(x) + 1/(x⁴+1). The limited-integration rule (a coefficient of logⁿ whose
      integral has residues outside C is not elementary) covers it unchanged: log(x)/(x⁴+1) →
      NotElementary (dilogarithm).
    * T2: `log_to_atan_sqrt(a, b, e)`: LogToAtan(U, √e V) without adjoining √e (parity: every
      pⱼ = √e uⱼ; two states even/odd on the rational parts), so it runs over K[θ] at any tower level.
      Used in `tower_quad_terms` (d < 0) and, replacing R3's ℚ(√e) detour, in `quad_terms`. E.g.
      exp(x)(−e²ˣ−3)/(e⁴ˣ−4e²ˣ+9) and (−log²x−3)/(x(log⁴x−4log²x+9)): the answers no longer jump
      by π (max step 2.2 before). Tower atans with e = 1 no longer print `sqrt(1)`.
    Not changed: ExtQuadPair (Step 7, over ℚ(i)) and the real-form output of trig towers; RootSums
    of degree > 2 inside towers are still refused.
    Tests: LogToAtan testset (identity for `log_to_atan_sqrt`); both packages: six tower integrands
    (derivative, continuity on fine grids, no `sqrt(1)`), log(x)/(x⁴+1) not elementary.
* **RT: RootSums inside towers** (2026-10-14, done, tests green; C = ℚ). In `residue_logs` the
  residue polynomial left after rational roots is factored (`factor_Q`); quadratic factors go to
  `tower_quad_terms`, the rest to `tower_root_sums`: `d5_gcd` over K = Kᵢ₋₁ (ℚ is algebraically
  closed in K, so splits of m are over ℚ, read back with `dconst_value`) gives `TowerRootSum(i, mq,
  W, deriv)`, W θ-major with coefficients in K[z]/m. Exact derivative (`tower_rootsum_derivative`):
  norm N = res_z(m, W) over Kᵢ, cofactor N/W mod m, δW = coefficientwise derivation + ∂_θW·Dθ,
  Tr(z·δW·N/W)/N with `power_sums`. Exp levels: correction Tr(α)·deg W (`rootsum_corr`), e.g.
  1/(e³ˣ+eˣ+1) = x + RootSum(…). Base-level RootSums inside a tower (exp(x) + 1/(x³+x+1)) become
  `BaseRootSum` (derivative from `rootsum_derivative`). `check_tower` uses the stored derivatives;
  `integrate_built` returns `IntegralWithRootSums` with `TermRootSum`s (new, exported: α-coefficients
  are terms of the user's package, e.g. `RootSum(α -> α*log((4/9 + log(x)) + (31/9)*α + …), …)`) or
  `RootSum`s (base level, `arg` = bd.x). `F(a)` evaluates both (`rs_value`). The limited-integration
  rule (coefficients of logⁿ with residues outside C → NotElementary) covers RootSum terms unchanged.
  Not covered: constant fields other than ℚ (trig towers over ℚ(i): `cos x/(sin³x+sin x+1)` is still
  `RischNotImplemented`); the real form (R2/R3) at tower levels: 1/(x(log⁴x+1)) is a quartic RootSum
  in log x, not the √2 log/atan form.
  Tests: test_risch.jl both packages (nine integrands: log/exp levels, nested log log, base-level in
  towers, Tr ≠ 0); test_integrate.jl "awaiting later stages" now uses the ℚ(i) case.
* **RF: real form of quartic residues at tower levels** (2026-10-14, done, tests green; C = ℚ).
  In `residue_logs`, an irreducible quartic factor goes first to `tower_quartic_real` (R2 at level
  i): `conj_pair_factors` gives d and the pairs (u, v) in ℚ(√d); W = gcd(D, A − (u+iv)δD) over the
  tower T3 with constants ℚ(i)(√d) (`change_constants`); U = (W + W̄)/2, V = (W − W̄)/(2i) are fixed
  by i ↦ −i and read back into T2 (constants ℚ(√d)); terms u log(U²+V²) + v·LogToAtan(U, V) (atans of
  polynomials in θ). `TowerRealForm(T2, logs, atans, corr, deriv)`: exact derivative computed in T2
  and mapped into T (error if not over ℚ), `corr` = Σ u·deg(U²+V²) for exp levels; output with
  `tower_to_term(b, T2, …)` (sqrt(d) constants). Otherwise the factor stays a RootSum (RT).
  E.g. 1/(x(log⁴x+1)) → √2/8 log(log²x+√2 log x+1) − … + √2/4 atan(√2 log x ± 1); exp(x)/(e⁴ˣ+1);
  exp(x)/(e⁴ˣ−e²ˣ+1) (√3); 1/(x log x (log⁴(log x)+1)). Pitfall: a parameter named `D` shadows the
  derivation `D(T, i, f)` (hence `Dn`).
  Tests: test_risch.jl both packages, seven integrands (no RootSum, sqrt present, continuity, derivative);
  the RT list now uses 1/(x(log⁴x+2)) (2^(1/4): stays a RootSum).
* **RC: RootSums over ℚ(i) in trigonometric towers** (2026-10-14, done, tests green). `residue_logs`
  (CT = ℚ(i)): after `ext_quad_terms`, a leftover residue factor becomes `tower_root_sums` (now generic
  in C; no factorisation over ℚ(i), `d5_gcd` copes with reducible m); base-level RootSums of a ℚ(i)
  tower (sin(x) + 1/(x³+x+1)) as in RT. Exact check in the complex tower as before. Output
  (`integrate_built`, complex branch): the RootSums stay complex — `complex_term_rootsum` writes each
  α-coefficient w as R + i·I, R = (w + σw)/2, I = (w − σw)/(2i) (σ: i ↦ −i, θ ↦ 1/θ; `real_term`),
  stored as (R, I) pairs in a `TermRootSum` whose poly is over ℚ(i) (printed `(a + b*im)`), e.g.
  cos x/(sin³x + sin x + 1) → RootSum(α -> α*log((−1 − 8/9 sin x + cos 2x + im*(sin 2x + 8/9 cos x)) + …),
  α³ − 3/31 α − 1/31 = 0). The elementary part is put in real form by `to_term_real`, checked against
  f − Re(Σ RootSum′) with Re = (d + σd)/2. `F(a)` = real part (`cvalue`, `cnum(::QI)`).
  Limitation: Re(α log W) jumps by 2π·Im α where W crosses the branch cut of the principal log, so
  F is an antiderivative only between those points (max step ≈ 1–1.7 on [0, 6] for the examples);
  a real form (pairing α with the conjugate data, Rioboo-style) would remove the jumps.
  Tests: test_risch.jl both packages, five trig integrands (derivative away from the jumps);
  test_integrate.jl "awaiting later stages" now uses residues over ℚ(e): 1/(x(log³x + log x + ℯ))
  (note: `exp(1)` is a Float64 in Julia; use `ℯ` for the symbolic constant).
* **RN: continuous numeric evaluation of RootSums** (2026-10-14, done, tests green; user's choice
  among: continuous trig answers via tan(u/2), real-valued LogToReal RootSums, or this). Finding: a
  real form would NOT remove the jumps at trig levels — LogToAtan needs polynomials in one real
  variable, and the existing Step 7 elementary trig answers jump too (max step on [0, 13]:
  1/(2+cos x) 1.81, 1/(5+3 sin x) 1.57, cos x/(2+sin²x) 1.11). Not changed here; a possible
  later step (tan(u/2) + LogToAtan, floor terms at u = π mod 2π).
  `F(a)` of an `IntegralWithRootSums` now continues each log W(α, x) along [x₀, a] from a fixed
  reference point x₀ (first of `RS_REFERENCE_POINTS` where every W is finite and nonzero):
  `continue_phase` accumulates angle(W(t)/W(s)), bisecting while a step exceeds 0.5 rad (depth ≤ 40);
  a zero of W on the path (a real pole of the integrand) is stepped over. `rs_numeric` gives the
  roots and x ↦ [W(α, x)] for `RootSum` (incl. `arg`) and `TermRootSum` (incl. ℚ(i) pairs).
  Printed answers and `rs(a)` (principal logs) are unchanged. Applies to all RootSum kinds.
  Tests: test_risch.jl both packages, six integrands: continuity (step 0.05) and F(b) − F(a) against
  Simpson's rule (atol 1e-8). Pitfall for test integrands: s³+s+2 = (s+1)(s²−s+2) has a real pole at
  sin x = −1; cos x/(sin³x+sin x+1) has real poles too.
* **TC: continuous trigonometric answers** (2026-10-14, done, tests green). In Step 7's real form
  (`real_log_pieces`) the piece −Im c·atan(V/U) (= −Im c·arg w) jumped where U = 0. When w is a
  polynomial in the level generator with constant coefficients (C = ℚ(i) or ℚ(i)(√d)),
  `continuous_arg_pieces` replaces it: z real (x at the base, θ at a real level): w = A(z) + iB(z),
  arg w ≡ −Σ atan(pⱼ(z)) by `log_to_atan(A, B)`; trig level θ = e^{iu}: t = tan(u/2),
  w = (1−it)^(−n) w̃(t), and with m = Σ_{odd deg pⱼ} sign(lc pⱼ) (the jumps at u = π mod 2π)
    arg w ≡ ((n − m)/2)·u − Σ atan(pⱼ(t)) + m·atan(t)      (continuous; no π, no floor)
  since −mπ⌊(u+π)/2π⌋ = −(m/2)(u − 2 atan(tan(u/2))). t = −i(θ−1)/(θ+1) is a tower element, so the
  pieces are differentiated and checked exactly in `to_term_real` (new piece kind :lin, optional
  printer as 4th tuple entry; `rpoly_term`, `real_field`, `re_part`/`im_part`, `real_sign`).
  `merge_pieces` now also merges the two halves of an ExtQuadPair. `tan` added to OPS (numeric eval).
  E.g. 1/(2+cos x) → (2/√3) atan(tan(x/2)/√3) − (2/√3) atan(tan(x/2)) + x/√3 (was a ratio-atan with
  jumps of 1.8). Falls back to the old atan(V/U) when w has non-constant coefficients or the
  constant field has generators (ℚ(i)(t)).
  Tests: test_trig.jl both packages, eight integrands: continuity on [−7, 13], F(13) − F(−7) against
  Simpson (crosses u = π several times), the textbook form for 1/(2+cos x).
* **TS: simpler trigonometric forms by Bioche's rules** (2026-10-14, done, tests green). `bioche`
  (called in `risch_integrate` after Stage 5c, before the ℚ(i) tower): f with a one-level ℚ(i) tower
  θ = e^{iu}, u = kx, constant coefficients, f = R(θ). Tests: R(1/θ) = −R → s = cos u; R(−1/θ) = −R →
  s = sin u; R(−θ) = R → s = tan u (in this order). g(s) via `sym_to_s` (symmetric Laurent →
  Chebyshev; sin through θ = iη) or `tan_to_s` (θ² = (1+is)/(1−is)); g ∈ ℚ(s) required. Exact checks:
  g(s(θ))·s′ = f in the tower, `check_result` for ∫g. Output: `to_term` with the base variable printed
  as sin(kx)/cos(kx)/tan(kx); for tan the jump correction J·(u − atan(tan u)), J = Σ c·σ over atans of
  odd degree at s = ±∞ (`atan_infinity_sign`; QuadAtan c√e, R2 terms over ℚ(√d)).
  Domain: g must have no poles in the range of s (`real_root_count`, Sturm; [−1, 1] or ℝ), else the
  general route (cot x keeps its |w|²-logs); log arguments negative on the range are negated, a
  QuadLog with a negative ratio becomes QuadLog(β, d, dV, U). Unresolved residues → general route.
  E.g. cos x/(2+sin²x) → (√2/2) atan(√2 sin x/2); cos³x/(2+sin x) → 2 sin x − sin²x/2 − 3 log(2+sin x);
  1/(1+sin²x) → (√2/2) atan(√2 tan x) + (√2/2)(x − atan(tan x)). Not covered: the half-angle cases
  (1/(2+cos x) stays TC), RootSums in s (cos x/(sin⁴x+2) stays RC).
  Tests: test_trig.jl both packages: nine integrands (form, atan count, continuity, Simpson), cot x.
  test_risch.jl: cos x/(sin⁴x+1) now gets a real form (√2, via s = sin x), so the RC/RN RootSum
  examples use cos x/(sin⁴x+2) and sin x/(cos⁴x+2) (2^(1/4): still RootSums).
* **TR: Bioche with RootSums** (2026-10-14, done, tests green). In `bioche`, residues of degree > 2
  of g(s) no longer send the integrand to the ℚ(i) route for s = cos u, sin u: `root_sums` in s with
  `arg` = the term cos(kx)/sin(kx) (exact check: derivative of the elementary part + Σ
  `rootsum_derivative` = g), returned as `IntegralWithRootSums(…, xk)`. A RootSum over ℚ, no `im`;
  F(a) is continuous (RN) since s stays in [−1, 1] where g has no pole, so the continued logs are a
  function of s. E.g. cos x/(sin⁴x+2) → RootSum(α -> α*log(sin(x) + 8α), α⁴ + 1/2048 = 0),
  cos x/(sin³x+2)² → sin x/(6(2+sin³x)) + RootSum(… sin(x) …). s = tan u with a RootSum keeps the ℚ(i)
  route (the jump at tan u = ±∞ is ∫_ℝ g, not available in closed form), e.g. 1/(sin⁴x+2cos⁴x).
  Tests: test_trig.jl (TS testset) both packages: four integrands (RootSum in sin/cos, no `im`,
  continuity, Simpson), the tan case.
* **RE: RootSums over ℚ(t₁, …) (e, log 2, …)** (2026-10-14, done, tests green). `rational_tfield(C)`
  (C <: Frac with base ℚ). `residue_logs`: a leftover residue factor over such C → `tower_root_sums`
  (generic; no factorisation, d5 copes). Base level (`integrate_el(T, 0, …)`, `integrate_built` L = 0):
  `root_sums` over C. Output: `TermRootSum` got a 4th field `pterms` (the polynomial's coefficients as
  terms via `cterm`, e.g. exp(1); used for printing and `rs_poly_numeric`); base-level RootSums over C
  become TermRootSums (`base_term_rootsum`: α-coefficients `poly_term` in x). Exact checks unchanged.
  E.g. 1/(x³+x+ℯ), 1/(x(log³x+log x+ℯ)), exp(x)/(e³ˣ+ℯ eˣ+1), exp(x) + 1/(x³+ℯ); SymEngine log(Basic(2))
  likewise (Julia's `log(2)` is a Float64 and is rationalised as input). Complex fields with generators
  (ℚ(i)(e)) still refused, e.g. sin(x) + 1/(x³+x+ℯ). (cos x/(sin³x+sin x+ℯ) ran > 100 s: fixed in SP.)
  Tests: test_risch.jl both packages, five integrands (TermRootSum, derivative, Simpson);
  test_integrate.jl "awaiting later stages" now sin(x) + 1/(x³+x+ℯ).
* **SP: residue resultant by interpolation** (2026-10-14, done, tests green). cos x/(sin³x+sin x+ℯ) ran
  > 100 s (also before RE): `residue_logs` computed R(z) = res_θ(D, A − zδD) by Euclid over K(z) with
  K = ℚ(i)(e)(x), normalising nested fractions at every step. `residue_resultant(D, A, dD)`: deg R ≤
  deg D, so R is evaluated at deg D + 1 points z = j·1 (each a resultant over K alone; points where
  A − z·dD drops below its formal degree are skipped) and interpolated (Newton). Used in
  `residue_logs`, `residue_poly` and `log_part`. Now refused in ~2 s (RischNotImplemented: RootSum
  over ℚ(i)(e)); test_risch.jl 46 s → 36 s, other files unchanged. The integral itself would need
  Bioche over ℚ(i)(t) (s = sin x gives 1/(s³+s+ℯ) over ℚ(e), handled by RE) — a possible next step.
  Tests: test_integrate.jl "awaiting later stages": the case is refused (no hang).
* **TE: Bioche over constant fields with e, log p** (2026-10-14, done, tests green). `bioche` is generic
  in C = ℚ(i) or ℚ(i)(t₁, …) with real generators (kinds :exp, :log; not :expi): θ-helpers
  (`θinv`, `θscale`, `sym_to_s`, `tan_to_s`) parameterised by C; g must lie in RC[s], RC = `real_ctype(C)`
  (ℚ or ℚ(t₁, …)), via `to_real` (exact: real constants have real coefficients in normal form) and
  `to_complex` back for the exact substitution check; k ∈ ℚ read through `to_real`/`crational`.
  Sign decisions (no pole of g in the range: `real_root_count` with a sign function; sign of log
  arguments at s = 0) use `csign`: exact over ℚ, else a 256-bit evaluation of the generators
  (`cbig`), undecided (→ general route) within 1e-40 of 0 — only the choice of form depends on it.
  Output Builders carry `T.consts`; RootSums over RC ≠ ℚ become TermRootSums (`base_term_rootsum`).
  E.g. cos x/(sin³x+sin x+ℯ) → RootSum in sin x over ℚ(e) (was refused after SP, > 100 s before);
  sin x/(ℯ+cos x) → −log(ℯ+cos x); sin x/(cos x−ℯ) → −log(ℯ−cos x); cos³x/(ℯ+sin x) →
  ℯ sin x − sin²x/2 + (1−ℯ²) log(ℯ+sin x). cos x/(ℯ+sin²x) gives a quadratic RootSum (√ℯ ∉ ℚ(e)).
  Not covered: tan rule with a RootSum (1/(sin²x+ℯ), refused over ℚ(i)(e)) — done in TT.
  Tests: test_trig.jl (TS testset) both packages: four ℚ(e) integrands (form, continuity, Simpson);
  test_integrate.jl "awaiting later stages" now 1/(sin²x+ℯ).
* **TT: tan-rule Bioche with RootSums** (2026-10-14, done, tests green). G(tan u) with a RootSum jumped at
  tan u = ±∞ (the correction ∫_ℝ g has no closed form). Instead W(α, tan u) = cos(u)^(−n) W̃(α),
  W̃ = Σ w_k sin^k u cos^(n−k) u — bounded, nonzero on ℝ (W monic: W̃ = ±1 where cos u = 0) — so
  Σ α log W = Σ α log W̃ − (Σα) n log cos u: a `TermRootSum` in W̃ (continuous via F(a), RN) plus the
  real term −(Σα)·n/2·log(cos²u) (Σα ∈ RC), whose singularity cancels against the logs in tan u; atan
  jumps as before (`tan_jump_terms`, factored out). The s-integral is still verified exactly; W ↦ W̃
  is an identity. E.g. 1/(sin⁴x+2cos⁴x) → RootSum(α -> α*log(sin x + 40/3 cos x α + 512/3 cos x α³), …);
  1/(ℯ+sin²x) → RootSum over ℚ(e) (was refused); cos⁴x/(sin⁴x+sin x cos³x+2cos⁴x) has the log(cos²) term.
  `gcd` now makes remainders monic (same result; much less swell over ℚ(e)).
  Not covered / slow: RootSums of degree ≥ 4 over ℚ(e), e.g. cos⁴x/(sin⁴x+sin x cos³x+ℯ cos⁴x), run
  for minutes in `root_sums` (d5_gcd in (ℚ(e)[z]/m)[s]: coefficient swell). A fix would compute W by
  Lazard–Rioboo–Trager (subresultants S_j(z) by evaluation/interpolation in z, then mod R_j).
  Tests: test_trig.jl (TS testset) both packages: four integrands (TermRootSum, no `im`, log(cos²) term
  present or not, continuity, Simpson); test_integrate.jl: the 1/(sin²x+ℯ) refusal removed.
* **LR: Lazard–Rioboo–Trager for RootSums** (2026-10-14, done, tests green; motivating case not solved).
  `lrt_logs(m, D, A, dD)` (used by `root_sums` and `tower_root_sums`; falls back to `d5_gcd` on any
  surprise): R(z) = Π Q_j^j (`squarefree` of `residue_resultant`); for m_j = gcd(m, Q_j), W = S_j(α, s),
  the degree-j subresultant of D and A − zδD (Bronstein IntRationalLogPart), its content vanishing on
  Q_j removed (S_j / Π gcd(L_k, Q_j)^k over the squarefree factors L_k of lc_s S_j), reduced mod m_j
  and made monic (`d5_monic`). S_j by evaluation at z = 0, 1, … (points where A − zδD drops degree are
  skipped) — `subresultant_coeffs` (Sylvester submatrix determinants, `field_det` = Bareiss,
  fraction-free) — and `interpolate` (Newton; factored out of `residue_resultant`), degree ≤ deg D − j.
  `gcdex` now keeps remainders monic too (Bézout cofactors scaled along). Exact checks unchanged.
  Suite times unchanged (test_trig 43 → 45 s, test_risch 35 → 39 s).
  Finding: cos⁴x/(sin⁴x+sin x cos³x+ℯ cos⁴x) still impractical: LRT itself 66 s, then
  `rootsum_derivative` minutes. Over ℚ(e) the residue factor m is not factored, so the residues of the
  1+s² part share a degree-6 m with the quartic ones; arithmetic mod m has coefficients of ~1200
  characters. Next: split D before the log part by its content w.r.t. the generators (D as a
  polynomial in e with coefficients in ℚ[s]: the gcd of those is the e-free factor, here 1+s²),
  i.e. separate small residue polynomials.
  Tests: test_risch.jl exact testset: `lrt_logs` for three integrands incl. deg W = 2 (x/(x⁶+x²+1)),
  `field_det`.
* **SD: splitting the denominator by its generator-free factor** (2026-10-14, done, tests green).
  `log_part` over C = B(t) (`rational_tfield`): `tfree_factor(D)` clears the denominators of D's
  coefficients, writes D = Σ_k t^k E_k(s) with E_k ∈ B[s] and returns G = gcd_k E_k when
  0 < deg G < deg D. Then A/D = A₁/G + A₂/H (H = D/G, Bézout cofactors of H and G) and the log part is
  computed for each piece, so the residue polynomials stay separate and small. Exact checks unchanged.
  The motivating cos⁴x/(sin⁴x+sin x cos³x+ℯ cos⁴x) now takes ~4 s (SymEngine; minutes before):
  a quadratic + a quartic RootSum over ℚ(e) instead of one of degree 6.
  Not covered: the same split in towers (`residue_logs` over ℚ(t)), and splits that need inner
  generators only (G is the factor free of the outermost generator; a recursive split happens only
  through the recursive `log_part` calls).
  Tests: test_risch.jl (`tfree_factor`, residue degrees [2, 4]; both packages 1/((x²+1)(x⁴+x+ℯ)));
  test_trig.jl TT list: the ℚ(e) tan-rule case.
* **ST: SD inside towers** (2026-10-14, done, tests green). `residue_logs` over ℚ(t₁, …):
  `tower_tfree_factor(T, i, D)` specialises the outermost generator to two rationals (a ring map on
  the constants via `change_constants`/`map_constants`, only to find a candidate; a bad point is
  skipped), takes G = gcd of the two images of D, lifts it back (constants in B, `kconst`) and accepts
  it only if G | D exactly; then A/D = A₁/G + A₂/H and `residue_logs` on each part. Also
  `tower_rootsum_derivative`: the norm N(θ) = res_z(m, W) is interpolated from resultants over K at
  θ = 0, 1, … (m monic: Π W(α) at every point) instead of Euclid over Kᵢ (82% of the time before).
  E.g. 1/(x(log²x+1)(log⁴x+log x+ℯ)), exp(x)/((e²ˣ+1)(e⁴ˣ+eˣ+ℯ)): > 90 s → ~3 s (warm).
  Tests: test_risch.jl RE list, both packages (derivative now with atol 1e-9 for tiny values);
  test_risch 44 → 56 s.
* **TH: half-angle shortcuts** (2026-10-14, done, tests green). In `continuous_arg_pieces` (trig level,
  constant coefficients) the winding number s = (n − m)/2 of w is known from TC; for integer s,
  `shifted_arg_pieces`: arg w = s·u + arg v, v = θ^(−s) w = A + iB (A = (v + σv)/2, B = (v − σv)/(2i),
  real trig polynomials). If A never vanishes on ℝ, arg v ≡ atan(B/A); else if B never does,
  −atan(A/B); else the TC tan(u/2) form. "Never vanishes" exactly: A·(1+t²)^K = Σ a_k (1+it)^(K+k)
  (1−it)^(K−k) has no real roots (`real_root_count`, Sturm, `real_sign` over ℚ or ℚ(√d)) and A(π) ≠ 0.
  The atan argument is printed as real_term(B)/real_term(A) (printing the reduced B/A would square
  the conjugate denominator). Pieces still differentiated and checked in `to_term_real`.
  E.g. 1/(2+cos x) → x/√3 − (2/√3) atan(sin x/(2+√3+cos x)); 1/(5+3 sin x) → x/4 + ½ atan(cos x/(3+sin x));
  1/(3+sin 2x) → (√2/4)x + (√2/4) atan(cos 2x/(3+2√2+sin 2x)). Not changed: Bioche tan-rule answers
  (1/(1+sin²x) keeps atan(√2 tan x) + correction).
  Tests: test_trig.jl TC testset (four integrands: one atan, no tan(…)); the TC loop checks "atan".
* **TB: tan-rule Bioche answers in the TH form** (2026-10-14, done, tests green). In `bioche`, for
  s = tan u without RootSums, the general route (`build_tower` + `integrate_built`, i.e. TC/TH) is
  tried first and used when it is elementary (not an `IntegralWithRootSums`) and TC needed no tan(u/2)
  form (counter `HALF_ANGLE_FORMS`, incremented in `continuous_arg_pieces` when TH fails at a trig
  level); otherwise the tan-rule answer as before. E.g. 1/(1+sin²x) → (√2/2)x − (√2/2) atan(sin 2x/
  (cos 2x − 3 − 2√2)); 1/(sin⁴x+cos⁴x) → √2 x − (√2/2) atan(sin 4x/(3+2√2+cos 4x)); 1/(3+sin x cos x) →
  (2/√35)x + (2/√35) atan(cos 2x/(6+√35+sin 2x)). Kept: 1/(2+sin²x) + 1/(3+cos²x) (the general route
  gives a ℚ(i) RootSum there). Cost: tan-rule integrands are integrated twice (test_trig 66 → 73 s).
  Tests: test_trig.jl TS list (three tan-rule entries: one atan, "sin("), the kept tan form.
* **TF: cot, sec, csc** (2026-10-14, done, tests green; user request). `parse_tower` reads them like
  tan through θ = exp(i·u): cot = i(θ + 1/θ)/(θ − 1/θ), sec = 2/(θ + 1/θ), csc = 2i/(θ − 1/θ); added to
  `TRIG`, `NONRATIONAL`, `has_trig` and `OPS` (numeric evaluation). Stage 5c refuses them (not
  polynomial in sin/cos), Bioche/general route as for any rational trig integrand. E.g. cot x →
  log(2 − 2cos 2x)/2, sec x → log(2 + 2 sin x)/2 − log(2 − 2 sin x)/2 (real poles: the |w|²-logs of
  Step 7, valid on both sides), sec x tan x → 4 cos x/(2 + 2cos 2x). Forms are not simplified
  (sec²x → 2 sin 2x/(2 + 2cos 2x) = tan x).
  Tests: test_trig.jl, both packages, twelve integrands (derivative at points avoiding the poles).
* **TA: atan as a primitive monomial** (2026-10-14, done, tests green; user request). New level kind
  `:atan` (`make_atan`, parsed from `atan(u)`): θ' = u'/(1 + u²) ∈ K. Refused (RischNotImplemented)
  when θ' is a ℚ-combination of x', exp arguments' and log/atan generators' derivatives — such
  identities hold only up to an undetermined, possibly piecewise constant (atan(tan x) = x,
  atan(1/x) = π/2 − atan x) — and atan of a nonzero constant (needs π). Treated as primitive (like
  log) in `rde`, `rde_general`, `rde_degree_bound`, `prde`, `prde_poly`, `poly_rde_reduced`,
  `integrate_poly_t`, `integrate_el`; skipped in the `make_exp`/`make_log` bases (exp(ρ atan) is
  new; atan' is no log-derivative) and in the log-derivative candidate lists (`logderiv_solve`,
  `cancellation_exponent`). In `integrate_log_poly` at an atan level, atan terms of ∫ lc(p) join the
  target c θ', and logs already in the tower (`log_element`, e.g. log x = θ₁) move into the
  polynomial part. NotElementary is downgraded to RischNotImplemented when the tower has an atan level
  (the structure arguments are for exp/log towers). E.g. atan x → x atan x − ½ log(1+x²);
  atan(x)/(1+x²) → atan²x/2; atan(log x)/x → log x atan(log x) − ½ log(1+log²x);
  exp(atan x)/(1+x²) → exp(atan x). Refused: atan(x)/x, atan(x) log x, atan(eˣ) (dilogarithms).
  asin, acos: step AS.
  Tests: test_integrate.jl "atan (step TA)", both packages (ten integrands, three refusals).
* **AS: asin, acos by the substitution u = sin t / cos t** (2026-10-14, done, tests green; user request).
  `risch_integrate` first collects asin/acos subterms (`collect_arcs`); all must be of one kind (mixing
  needs π) with one linear u = a x + b. `integrate_arcsin` rebuilds the integrand in the user's package
  with x as t (asin: x ↦ (sin x − b)/a, asin(u) ↦ x, √(1−u²) ↦ cos x, times cos x/a; acos: cos/sin
  swapped, times −sin x/a; principal branches), integrates it by `risch_integrate` (verified there),
  and maps the answer back (`back`): x ↦ asin(u), sin(kx), cos(kx), tan(kx) (k ∈ ℤ) and tan(x/2)
  through (cos t + i sin t)^k computed exactly as A(u) + B(u)·√(1 − u²) (pairs with r² = 1 − u²).
  Also integrands whose only radicals are q^(k/2), q = K(1 − u²) with √K rational (completing the
  square, `unit_circle_radicand`) go this way first (fallback: the radical route), and the answer
  reuses the integrand's radical (√q/√K). `term_rebuild` rebuilds terms through `OPS`; asin, acos added
  to `OPS`. Correctness: chain rule + the identities sin(asin u) = u, cos(asin u) = √(1−u²) on −1 < u < 1.
  E.g. asin x → x asin x + √(1−x²); asin²x → (asin²x − 2)x + 2 asin x √(1−x²); 1/√(1−x²) → asin x;
  √(1−x²) → ½ asin x + ½ x√(1−x²); 1/√(x−x²) → asin(2x−1); √(4−x²) → 2 asin(x/2) + x√(4−x²)/2.
  Not covered: RootSums after the substitution, √K irrational (√(2−x²) keeps the Euler form),
  asin of non-linear arguments; like terms are not collected (x² asin x).
  Tests: test_integrate.jl "asin, acos (step AS)", both packages (17 integrands, forms, refusal).
* **AC: acot, acsc, asec** (2026-10-14, done, tests green; user request; domain u > 1 for acsc/asec by
  the user's choice). acot(u) ↦ atan(1/u) (`rewrite_acot`; Julia's definition for all u ≠ 0), then TA;
  together with atan(u) it is refused (π/2). acsc(u) = asin(1/u), asec(u) = acos(1/u): the AS
  substitution in a reciprocal mode (`recip` in `integrate_arcsin`): 1/u = sin t (cos t), x ↦
  (1/p − b)/a, dx = ∓r/(a p²), √(u² − 1) ↦ r/p (u > 0); mapped back with s = 1/u (A(1/u) as a rational
  function of u) and √(1 − 1/u²) = √(u² − 1)/u. The original acsc/asec terms stay in the answer.
  Valid for u > 1 (principal branch t ∈ (0, π/2)); on u < −1 some terms have the wrong sign.
  New `tidy_terms` on the mapped-back answers (also AS): rational factors of products/quotients/powers
  multiplied into one canonical ℚ(x) factor, a rational factor distributed over a single sum, and sum
  terms with the same non-rational part collected. E.g. asec x → x asec x + ½ log(2 − 2√(x²−1)/x)
  − ½ log(2 + 2√(x²−1)/x); x asec x → x²/2 asec x − ½√(x²−1); x² asin x → x³/3 asin x + (2/9 + x²/9)√(1−x²).
  Not covered: radicals written as √(1 − 1/u²).
  Tests: test_integrate.jl "acot, asec, acsc (step AC)", both packages (eight integrands, forms, refusals).
* **SY: symbolic parameters** (2026-10-14, done, tests green; user request). A leaf that is neither x,
  e nor a number becomes a new indeterminate of the constant field: `ConstGen(:sym, 0, term)` (new
  field `term`; equality by name), added via `NewConstants` like e / log p (step 6); printed back as the
  user's symbol (`constgen_term`). Answers hold for generic parameter values (as usual in a CAS).
  `csign` is undecided (nothing) when a parameter is present, so numeric sign decisions fall back.
  Powers with a non-rational constant exponent (x^a, x^ℯ) are now exp(k·log u) instead of refused.
  New `quad_factor_t!`: a quadratic residue factor over ℚ(t₁, …) with roots α ± iβ, α, β in the field
  (−Δ a square: `csqrt`), gets the real log + LogToAtan form, computed over ℚ(i)(t₁, …) (`cplx_type`,
  W = U + iV by conjugation, `to_real`) — e.g. 1/(x²+a²) → atan(x/a)/a, a/(1+x²) → a atan x,
  1/((x+a)²+b²) → atan((x+a)/b)/b, and also 1/(x²+ℯ²) → atan(x/e)/e (was a RootSum). The Bioche tan
  jump correction takes the field's sign function (`tan_jump_terms(…, sg)`; undecided → general route).
  Works in both packages (SimpleExpressions `@symbolic x p`, SymEngine symbols). E.g. x·exp(a x) →
  exp(a x)(x/a − 1/a²); x^a → x exp(a log x)/(1 + a); atan(a x) → x atan(a x) − log(1/a² + x²)/(2a).
  Cap: at most `MAX_PARAMS` parameters (2 in SY, 4 since PF; RischNotImplemented beyond). Each parameter nests the
  constant field one level deeper and the normalising gcds grow steeply: in test_apostol.jl,
  (c sin x + d cos x)/(a sin x + b cos x) (four parameters) did not finish in minutes, and three-parameter
  integrals took ~1 min. With the cap test_apostol.jl completes: 148/175 (HEAD before SY: 139), 98 s
  (47.5 s before; the extra time is the newly passing parameter integrals, the slowest
  1/(a² sin²x + b² cos²x) at 23 s). The monic-remainder `gcd` (TT) is not the cause (without it that
  case took > 9 min).
  Not covered: constants exp(a) (refused: would need exp(a) as a further generator with its relations),
  asin of a·x with symbolic a (AS needs rational coefficients), sign/branch-dependent forms.
  Tests: test_integrate.jl `sy_tests`, both packages (14 integrands, the atan form, exp(p) refused);
  test_risch.jl SD test: only the quartic is left unresolved; test_trig.jl TS list expectation.
* **DL: dilogarithms with PolyLog.jl** (2026-10-14, done, tests green; user request). New dependency
  PolyLog (Project.toml, test/Project.toml + Manifest). When `integrate_log_poly` decides NotElementary
  at θ = log(a x + b) (one log level over ℚ(x), a, b ∈ ℚ, degree 1 in θ), `dilog_split` takes the simple
  poles c ∈ ℚ of the θ-coefficient r (residue ρ, K = a c + b ≠ 0) out as `DilogTerm`s and the rest goes
  through the normal algorithm again (if that still fails: the original NotElementary):
    K > 0: ρ(log K · ½ log(s²) − Li₂(−a s/K)),   K < 0: ρ(½ log²(a s) + Li₂(−K/(a s))),   s = x − c,
  each with derivative ρ θ/(x − c) on a x + b > 0 (stored for the exact check, as SpecialTerm).
  Printed with `PolyLog.li2` (`OPS[:li2]` also for numeric evaluation); a symbolic package without a
  method for li2 gets NotElementary (the integral is not elementary; the dilog form cannot be built).
  `opname` now uses `nameof` for callable non-Function operations (SymEngine's SymFunction("li2")).
  E.g. log(1+x)/x → −li2(−x); log(x)/(1−x) → li2(1−x); log(x)/(1+x) → ½ log²(1+x) + li2(1/(1+x)).
  Needs, in the packages: SimpleExpressions an extension like its SpecialFunctions one
  (`PolyLog.li2(z::AbstractSymbolic) = SymbolicExpression(PolyLog.li2, (z,))`), SymEngine e.g.
  `PolyLog.li2(z::Basic) = SymFunction(:li2)(z)`; the tests define these stand-ins (end of
  test_integrate.jl, after the tests that expect NotElementary without them).
  Not covered: irrational poles (log(1+x)/(1+x²): NotElementary), several logs, Li₃ and higher.
  Tests: test_integrate.jl `dl_tests`, both packages (seven integrands, the −li2(−x) form, a refusal).
* **NR: nested-radical real forms** (2026-10-14, done, tests green). In `quartic_real!` (R2), a conjugate
  pair u ± iv with u, w = v² ∈ ℚ(√d), w > 0 (`real_sign`) but v ∉ ℚ(√d) (`qs_sqrt` fails), e.g. the
  residues of 1/(x⁵+1) (Im ζ₁₀ = √(10 − 2√5)/4): `quartic_nested` computes W = gcd(D, A − (u + y)D′),
  y² = −w, by `d5_gcd` over ℚ(√d) with modulus z² + w (irreducible since −w < 0); W = U + yV′,
  so V = √w V′ and the pair is u log(U² + w V′²) + Σ 2√w atan(√w uⱼ) (`log_to_atan_sqrt(U, V′, w)`,
  uⱼ over ℚ(√d)). New `QuarticNested{S}` (logs, nested atans (c, w, u) = c √w atan(√w u)) with
  `derivative_of` (c w u′/(1 + w u²) ∈ ℚ(√d)(x)) and `to_term` (√w printed as sqrt(a + b√d)); exact
  check via `qs_down` as for R2; in towers through `BaseTerms`; Bioche's tan jump correction counts
  its atans (c σ √w). E.g. 1/(x⁵+1) → log(1+x)/5 + ((√5−1)/20) log(x² + ((√5−1)/2) x + 1) − … +
  2√(1/40 + √5/200) atan(√(1/40 + √5/200)(…)) + …; also x/(x⁵+1), x³/(x⁵+1).
  The same at tower levels: step NT. Not covered: roots needing 2^(1/4) or deeper nesting (1/(x⁴+2), 1/(x⁴+x²+3) stay RootSums), degree ≥ 6.
  Tests: test_risch.jl (exact: three quintic integrands, QuarticNested present; both packages: no
  RootSum, sqrt present, continuity, Simpson); the R2 "stays RootSum" example is now 1/(x⁴+x²+3).
* **IT: iterated integrals with RootSums** (2026-10-14, done, tests green). `integrate(f, x, y)` (the
  wrapper calls `risch_integrate` repeatedly) now accepts an `IntegralWithRootSums` as the integrand:
  `risch_integrate(F::IntegralWithRootSums, y)` integrates the elementary part normally (x a parameter,
  SY), a RootSum free of y to y·RootSum, and c(y)·RootSum to (∫ c dy)·RootSum (new `ScaledRootSum`,
  printed `(c)*RootSum(…)`, evaluated through `rs_value`/`rs_value_continuous`); a RootSum whose roots
  or logs depend on y is refused (`depends_on`, `has_leaf`). To make c(y)·RootSum visible,
  `risch_integrate` now first pulls out of a top-level product/quotient the factors that are free of x
  and contain a symbol (`split_free_factor`, `has_symbol`): ∫ c g dx = c ∫ g dx — this also keeps such
  parameters out of the constant field (faster) and lets exp(p)·x integrate (exp(p) as a factor).
  Definite integrals: `F(x => value)` evaluates an `IntegralWithRootSums` at a numeric value (the
  wrapper's `∫f(x=>b) - ∫f(x=>a)`), with RN's continuous branch.
  E.g. ∫∫ y/(x³+x+1) dx dy = (y²/2)·RootSum(…); ∫∫ exp(y)/(x³+x+1) dx dy = exp(y)·RootSum(…).
  Not covered: RootSums depending on y (1/(x³+y)), integrating a RootSum again in its own variable.
  Tests: test_integrate.jl "iterated integrals (step IT)" (SymEngine: forms, ∂²F/∂x∂y = f, refusal,
  a definite integral); SY test: exp(p)·x now integrates.
* **NT: nested-radical real forms at tower levels** (2026-10-14, done, tests green). `tower_quartic_real`
  (RF) now also takes conjugate pairs u ± i√w with √w ∉ ℚ(√d): `tower_quartic_nested` computes, over
  T2 (the tower over ℚ(√d)), W = gcd(D, A − (u + y)δD), y² = −w, with `d5_gcd` (modulus z² + w over
  K₂ = T2.Ts[i]); W = U + yV′ gives u log(U² + wV′²) + Σ 2√w atan(√w pⱼ) with `log_to_atan_sqrt(U, V′, w)`
  (pⱼ ∈ K₂[θ]); exp correction Σ u·deg(U² + wV′²); derivative computed in T2 (atans: c w p′/(1 + w p²))
  and read back into T. `TowerRealForm` has a new field `natans` (c, w, p) printed c √w atan(√w p).
  E.g. 1/(x(log⁵x+1)), eˣ/(e⁵ˣ+1), log x/(x(log⁵x+1)), 1/(x log x (log⁵(log x)+1)): no RootSum.
  Tests: test_risch.jl both packages (three integrands: no RootSum, sqrt present, continuity, Simpson).
* **PF: faster fraction arithmetic (Henrici)** (2026-10-14, done, tests green; was the "Later" item).
  `Frac` `+` and `*` use Henrici's algorithms: a/b + c/d with G = gcd(b, d), t = a(d/G) + c(b/G),
  h = gcd(t, G) → (t/h)/((b/G)(d/h)) (no gcd at all for coprime or trivial denominators, `frac(a + c, b)`
  for equal ones); (a/b)(c/d) = ((a/g₁)(c/g₂))/((b/g₂)(d/g₁)) with g₁ = gcd(a, d), g₂ = gcd(c, b);
  `inv` and integer multiples without gcd. Same normal form as before (coprime, monic denominator), so
  equality and every exact check are unchanged. Effect (all levels of nesting, not only parameters):
  1/(a² sin²x + b² cos²x) 23 → 5.6 s, xⁿ⁻¹ sin(xⁿ) 10.6 → 4.2 s, e^(ax) cos bx 6.7 → 1.6 s;
  test_tower 31 → 16 s, test_risch 61 → 43 s, test_trig 73 → 58 s; test_apostol.jl 98 → 50 s and
  149/175 with `MAX_PARAMS` raised from 2 to 4 (the four-parameter (c sin x + d cos x)/(a sin x +
  b cos x), which did not finish in minutes, now takes ~4–8 s).
  A fraction-free representation was considered and dropped (2026-10-15): once compiled, all 175
  Apostol integrals take 1.0 s together (53.6 s cold), the slowest 0.4 s; the cost is compilation,
  not arithmetic. (Reusing the tower across `bioche`, TB and the general route was tried and
  reverted, see PC.)
  Tests: test_integrate.jl SY tests: three parameters integrate, five are refused.
* **PC: precompile workload** (2026-10-15, done, tests green). Tried first: building the tower once and
  sharing it (and the general-route integral) between `bioche`, its TB check and `risch_integrate`.
  No measurable gain (Apostol set 50 → 49 s, trig cases unchanged), reverted: once compiled,
  1/(a² sin²x + b² cos²x) takes 0.18 s (tower 0.003 s, integral 0.17 s); the rest of its ~5 s is
  compiling the algebra for the nested field types. (For the same reason skipping the rational
  integrator before TB's check would gain little.) So: a PrecompileTools workload at the end of
  `module Risch` (new dependency PrecompileTools, also in test/Project.toml), 20 integrals on `Expr`
  terms with an `Expr` builder (exp/log/rational with RootSum, trig incl. half-angle, parameters,
  radicals, asin, atan, erf, Si, Ei). It runs only during precompilation, so the tests (which
  `include` Risch.jl) are unaffected. Effect, fresh session with SimpleExpressions, first call:
  x eˣ 6.8 → 2.3 s, 1/(x³+1) 5.3 → 1.9 s, 1/(1+cos²x) 7.9 → 2.4 s, eˣ sin x 3.8 → 1.1 s,
  1/(a² sin²x + b² cos²x) 9.1 → 3.1 s; load 0.1 → 0.4 s; package precompilation 1 → 27 s. The
  remaining ~2 s is code specialized on the term type (parsing, building), which a workload in a
  package extension per term package (weak dependency) could cover.
* **US: u-substitution (derivative-divides)** (2026-10-15, done, tests green). When the direct routes
  throw RischNotImplemented or NotElementary, each subterm u of f (outermost first; not x, not of
  degree ≤ 1 in x) is tried: q = f/u' (u' by the chain rule on terms, `term_deriv`; integer powers
  as p b^(p-1) b', radicals as p b^p b'/b so the radical itself reappears) is parsed into a tower
  over x with the parse hook `usub_hook`: u, and every subterm whose x occurs only inside u, become
  opaque constants (`:sym` generators, via `sym_const` factored out of `parse_tower`); for
  u = v^e also v = U^(1/e), v^(ke) = U^k; for u = x^k also x^(mk) = U^m. If q is a constant
  there, f = G(u)·u' exactly (formally independent constants: the identity survives putting the
  functions of u back). G is printed with u ↦ x, integrated in x (verified there; at most two
  nested substitutions, `USUB_DEPTH`) and the answer printed with x ↦ u (as in AS). A RootSum
  after the substitution is not mapped back (the candidate fails). If no candidate works, the
  original exception is rethrown. `risch_integrate` is now this wrapper around `integrate_direct`.
  E.g. cos 2x √(4 - sin 2x), x⁵/√(1 - x⁶), x/(√(1+x²)√(1+√(1+x²))), √(1+3cos²x) sin 2x,
  log x/(x√(1+log x)), √(1+√x), x/(1+x⁴), and x e^(x²)/(1+x²) = Ei(1+x²)/(2e).
  Apostol set 149 → 154 (9, 14, 20, 55, 66; 163 reaches Ei, which SimpleExpressions cannot build);
  still failing: sin x/√(cos³x) (G = -1/√(U³): radicand U³ not supported), #19 (elliptic).
  Cost: failing integrals try every candidate (test_integrate 63 → ~70–80 s, mostly in testsets that
  check refusals, plus compiling the new code; the Apostol set 49 → 59 s).
  Tests: test_integrate.jl "u-substitution (step US)"; the nested-radical refusal is now
  √(x + √(x + 1)) (√(1 + √x) integrates by u = √x).
* **WR: Symbolics.jl check; opaque leaves, rational leaves, a Hermite bug** (2026-10-15, done, tests
  green). Ran the Apostol set with Symbolics.jl variables (scratch script, not a testset):
  - Symbolics' `Num` wrapper has `iscall == false`, so the whole integrand was a leaf, taken as a
    parameter: ∫ f dx = f·x, "verified" (f is a constant to the tower). All 175 "succeeded", wrong.
    Guard (`check_leaf`, `check_leaves` at the entry of `risch_integrate` and in the parameter branch
    of `parse_tower`): a leaf other than x whose printed form mentions x as a token
    (`mentions_var`) raises RischNotImplemented. Not in `sym_const` (US uses it for such subterms).
  - Hermite reduction (`hermite_reduce`) bug: the new numerator is C + U B'/j with U = D/V^(j+1)
    (Bronstein: A ← C − U B'/(1−j)); the code had C + B'/j. Wrong only when B' ≠ 0 (deg V ≥ 2) and
    U ≠ 1, e.g. 1/((x-1)(x²+1)²), 1/((x²+1)(x²+2)²): these raised the self-check RischError.
    Also used for tower levels (δ), so fixed there too.
  - `leaf_rational` reads Symbolics' numeric leaves "(1//3)" (one pair of parentheses stripped,
    `//` accepted); before, they became parameters, so e.g. the asin route (AS) refused 1/3 + 2x/3.
  With `Symbolics.unwrap` on input: 166/175 integrate, all numerically correct (SimpleExpressions:
  154; Symbolics has Ei). Open: 20 of those answers contain floats or approximated rationals
  (e.g. √2/8 ↦ 38613965//218433572): the default `lift` is `identity` for Symbolics, so sqrt(2) is
  evaluated by Julia. Needs a Symbolics-specific build/lift (unevaluated sqrt(2)) and Num
  unwrap/rewrap, i.e. a package extension.
  Tests: test_risch.jl "Hermite reduction: repeated factor of degree ≥ 2 with other factors",
  "opaque leaves and rational leaves (step WR)".
* Out of scope (separate projects): RootSum for residues of degree > 2; the algebraic Risch algorithm
  (Trager / Bronstein vol. II: integral bases, places, divisors) for general algebraic integrands.

### The constant-field interface (what a new `C` must implement)

| function | meaning | ℚ method | fallback |
|---|---|---|---|
| `cfromQ(C, q)` | embedding ℚ → C | identity | `RischNotImplemented` |
| `crational(c)` | `c` as a rational if `c ∈ ℚ`, else `nothing` | identity | `RischNotImplemented` |
| `cflat_all(C, cs)` | coordinates over ℚ of a list of constants | `[[c] for c]` | `RischNotImplemented` |
| `constant_roots(p)` | distinct roots in C of `p ∈ C[z]` (may be incomplete, see its docstring) | `rational_roots` | `RischNotImplemented` |
| `cterm(b, c)` | the constant as a term of the user's package | `b.lift(num(c))` | `RischNotImplemented` |

plus field arithmetic (`+ - * inv / zero one iszero isone ==`, `Integer * c`). `solve_columns` and
`rde_base` are generic over the field. `build_tower(f, xk; constants = Q)` selects the field.
Fallbacks raise rather than guess: e.g. `crational` answering "not rational" for a constant that is
rational in disguise would silently break the integer test for the cancellation exponent `i0` in `rde`.

## 0. Ground rules (unchanged from the previous session)

* Since 2026-10-14 the session runs on the user's Mac with Julia 1.13 (juliaup) and all packages installed:
  the assistant runs the five test files itself (`julia test_X.jl`). Still: small steps, every step ends with all four test files green, and every
  integration result stays *self-verified by differentiation* in the exact field.
* Two symbolic packages must keep working: SimpleExpressions.jl (expressions are callable `Function` subtypes,
  constants like `-1` are callable objects, constant-only calls are evaluated eagerly by Julia) and SymEngine.jl
  (`Basic <: Number`; `exp(x)` is the power `E^x` and `E` prints as `exp(1)`; sums are unordered; it merges
  `exp(a)*exp(b)` into `exp(a+b)`). Only `iscall`, `operation`, `arguments` are used from TermInterface.
* Never evaluate constants numerically: results are built by *calling operations as functions* through the
  `Builder(build, lift, x)`; constant-only calls such as `sqrt(3)` go through `deferred_call`
  (substitution `u(value, :)`), `lift` converts numbers to the package's type (`Basic`).
* `NotElementary` = decided by the algorithm; `RischNotImplemented` = not handled. Do not claim the former
  unless the theory covers the case. Known soundness gap: the tower RDE (`rde`) handles only
  polynomial/Laurent shapes and constant cancellation; its bounds can lose a solution, so a
  `NotElementary` raised from there is only as good as those bounds (step 8 closes this).

## 1. Why refactor

Everything that is left needs a constant field other than ℚ *under the whole tower*:

| feature | constants |
|---|---|
| 5b quadratic residues inside towers | ℚ(√d) |
| 5d `exp(x+1)`, `log(2x)`, `sin(x+1)`, `exp(x)+exp(x+1)` | ℚ(e), ℚ(log 2), ℚ(sin 1, cos 1) |
| 5c-ii general trig (`1/(2+cos x)`, `tan`) | ℚ(i) (+ real forms) |
| Risch-DE cancellation (general) | "constant" must mean `D c == 0` |

`Q = Rational{BigInt}` is hard-wired today in ≈56 top-level blocks (inventory at the end).

## 2. Design

**Two roles of `Q` must be separated.**
* `Q` stays the type of *exact rational numbers used as numbers*: exponents, multiplicities, integer degrees,
  coefficients of ℚ-linear relations (`solve_relation`), `num(c)` formatting, `rational_roots` input.
* `C` (new type parameter) is the type of *constants of the differential field*: coefficients of the base
  polynomials. Default `C = Q`; all current behaviour must be reproduced when `C = Q`.

**Core definitions** (names are suggestions)

```julia
# embeddings and predicates
cfrom(::Type{C}, q::Q)            # Q -> C        (identity for C = Q)
cone(C), czero(C)
cflat(c::C) :: Vector{Q}          # coordinates of a constant over Q (for flat/solve_columns)
# tower
struct Tower{C}  ...  Ts[1] = Frac{UPoly{C}}       # K_0 = C(x)
is_constant(T, f)  = iszero(D(T, f))               # replaces "const_value(f) !== nothing"
const_value(T, f)  :: Union{C,Nothing}             # kept, now returns C
kconst(::Type{C}, c)  # replaces kconst(c::Q)
lq(T, q::Q, j)        # lift rational number to level j (= liftto(T, kconst(C, cfrom(C,q)), j))
```

**Generic utility that unlocks 5b/5d/5c-ii: `change_constants(f, φ)`**: rebuild any tower element
(nested `Frac{UPoly{...}}`) with every base coefficient mapped by `φ : C -> C′`. Needed to run a
sub-computation (e.g. gcd for a quadratic residue) over `C′ = C(√d)` and to map the result back.

**Constant extensions are field extensions of C, not tower levels:**
* algebraic: `QS{d}` (ℚ(√d), already exists), `QI` (ℚ(i), already exists); compose by making the
  coefficient type of `QS` a parameter if ℚ(i,√d) is ever needed (not needed at first);
* transcendental (5d): `C = Frac{UPoly{Q}}` in an indeterminate `ε` standing for `e = exp(1)`; keep a registry
  `ε ↔ exp(c)` (and `log c`), and decide independence of new constants by ℚ-linear relations among their
  arguments exactly as `make_exp`/`make_log` already do for generators.

## 3. Ordered steps (each step: all four test files pass before continuing)

1. ✅ **Baseline.** Run all four test files, record results. Do not change anything.
2. ✅ **Introduce `C` as an alias only.** `const C = Q`. Rename roles: wherever a `Q` means "constant of the
   field" (coefficient types `QX = UPoly{Q}`, `QXF`, `kconst`, `const_value`, `lq`, `dx`, `integrate_poly`,
   `QI`'s parts stay Q), write `C`. Pure renaming, behaviour identical. Tests green.
3. ✅ **Make `C` a type parameter** of `QX`/`QXF` → `CX{C}`, `CXF{C}`, then of `Tower{C}`.
   `Tower(xk, scales)` gets a `C`. Functions get `C` from `T` (or from the argument's type). Still only `C = Q`
   is exercised. This is the big mechanical step (≈40 blocks); do it in groups: (a) algebra + Stage 1
   (`hermite_reduce`, `log_part`, `integrate_rational`), (b) tower construction (`make_exp/log`, `flat`,
   `solve_columns` using `cflat`), (c) integration (`integrate_el`, `residue_logs`, `rde*`), (d) front/back ends.
4. ✅ **`is_constant`.** Replace `const_value(f) !== nothing` tests by `is_constant(T, f)` where the meaning is
   "differential constant" (residue criterion in `residue_logs`, `make_log` constant ratio, `rde` cancellation
   test `i0`). Keep `const_value` for rational-only places (exponents). Tests green.
5. ✅ **`change_constants` + 5b.** Implement `change_constants`. In `residue_logs`, for an irreducible quadratic
   residue factor: extend `C → C(√d)`, compute `W = gcd(D, A - a·δD)` there, then return the same
   `QuadLog/QuadAtan`-style terms but with tower-element arguments (generalise `QuadLog`/`QuadAtan` to hold
   tower elements `U, V ∈ K[θ]`). Verification: derivative stays inside the base field (as in 5a).
   Add tests: `1/(x*(log(x)^2+2))` → `atan(log(x)/√2)/√2`, `exp(x)/(exp(2x)+... )` etc.
6. ✅ **5d constants.** Add the constant registry and the `Cε = Frac{UPoly{Q}}` field. Then
   `exp(x+1)` = `ε·exp(x)`, `log(2x)` = `log 2 + log x`, `sin(x+1)`. Update `make_exp/make_log/ep_linear`
   (the "nonzero constant" `RischNotImplemented`s), and the output builder (constants `exp(1)`, `log(2)` via
   `deferred_call`). Tests: `exp(x)+exp(x+1)`, `log(x)+log(2x)`, `∫exp(x+1)`, `sin(x+1)*x`.
7. ✅ **5c-ii.** With `C = QI`: general trig through `exp(ix)`, real-form output
   (`F = (v + conj(v))/2`, `θ^k + θ^-k → 2cos kx`, logs with complex residues → `atan`/`log` of norms).
   Needs `rational_roots` over `QI` (or restrict to residues in `ℚ(i)`) and `flat` over `QI`.
8. ✅ **Soundness work (optional, high value):** general cancellation in `rde` (Bronstein ch. 6, parametric
   logarithmic derivative), normal denominators in tower RDEs (6.2–6.3), limited integration (ch. 7).

9. **Full Risch DE in towers** (planned 2026-10-13, not started).

   *Why.* `rde` (tower case) only handles f, g polynomial (log) or Laurent (exp) in the top
   generator; otherwise it raises `RischNotImplemented` (normal denominators, simple poles of f).
   Typical refused case: an exp-polynomial coefficient with a normal denominator, e.g.
   ∫ exp(eˣ)·e^{2x}/(eˣ+1)² = exp(eˣ)/(eˣ+1) (elementary, refused today). The full machinery makes
   these decided (answer or proved `NotElementary`) and removes the "simple pole of f" refusals.

   *Pieces* (Bronstein section; what can be reused; rough size):

   | # | piece | does | reuses | size |
   |---|---|---|---|---|
   | 1 | SplitFactor (3.5) | normal / special parts of a denominator | `gcd`, tower `D` | small |
   | 2 | Weak normalisation (6.1) | remove simple poles of f with positive integer residues (y = q z) | residue machinery of `residue_logs` | small–medium |
   | 3 | Normal denominator (6.1) | h = gcd(e, e′)/gcd(p, p′); y = q/h gives a q′ + b q = c, a, b, c polynomial | idea of `rde_base`'s bound | medium |
   | 4 | Special denominator (6.2) | power of t in the denominator; exp has a cancellation sub-case | `cancellation_exponent` (8b) | medium |
   | 5 | Degree bounds (6.3) | base / primitive / exp cases with cancellation sub-cases | 8b (exp); primitive needs limited integration | medium |
   | 6 | SPDE (6.4) | reduce a q′ + b q = c to a = 1 (extended Euclid + recursion) | `gcdex` | small–medium |
   | 7 | No-cancellation solvers (6.5) | three cases by deg b vs deg a / δ(t) | — | medium |
   | 8 | Cancellation solvers (6.6) | primitive: recursive RDE in k + limited integration; exp: parametric log-derivative | 8b, `integrate_el` | medium–large |
   | 9 | Parametric RDE / limited integration (ch. 7) | y′ + f y = Σ cᵢ gᵢ, unknown constants cᵢ, over towers; complete primitive cancellation; fully general limited integration in `integrate_log_poly` | `rde_param_base` (8a, base level only) | large |

   Total roughly 500–800 lines (comparable to steps 5–7 together).

   *Staging* (each stage: all test files green; uncovered cases stay `RischNotImplemented`):
   * 9a: pieces 1–3 + 6 + the simple solvers (no cancellation). Keep the current Laurent `rde` as a
     fast path; call the new solver when `laurent_of` would refuse (normal denominators) or f has
     simple poles. Test: ∫ exp(eˣ)e^{2x}/(eˣ+1)², plus integrands whose exp-polynomial coefficients
     have normal denominators at log and exp levels, over ℚ and over ℚ(i) (trig).
   * 9b: pieces 4–5 (special denominator, degree bounds), wired to `cancellation_exponent`.
   * 9c: pieces 7–8 (full no-cancellation solvers, exp cancellation).
   * 9d (optional): piece 9 (parametric RDE in towers, primitive cancellation).

   *Risks.* Coefficients are tower elements: every bound must use the tower derivation and the
   generic constant fields (ℚ, ℚ(i), ℚ(√d), ℚ(t…)). No Julia in the assistant's sandbox: expect one
   or two test round-trips per stage, more fix rounds than before. Piece 9 is the hardest part of
   Bronstein (SymPy still has heuristic gaps there).

10. **Radicals by substitution** (planned 2026-10-13, not started; after step 9).

    *Why.* Today `sqrt`, `cbrt`, rational powers `u^(p/q)` and exp of a non-integer multiple of a log
    raise `RischNotImplemented`: the tower needs transcendental monomials, and exp(½ log x) = √x is
    algebraic over ℚ(x) (the structure theorem in `make_exp` detects it). The full algebraic Risch
    algorithm is out of scope; a front end of classical substitutions covers most textbook cases and
    reduces them to the existing transcendental machinery.

    *Rules* (each answer verified by differentiation in the original variable before it is returned):
    * x^r · p(x), r ∈ ℚ \ ℤ, p a polynomial (or Laurent polynomial): term by term, x^(r+k+1)/(r+k+1).
      More generally R(x, x^(1/n)) with one radicand x: substitute x = tⁿ (dx = n t^(n−1) dt).
    * R(x, ((ax+b)/(cx+d))^(1/n)) with R rational (one linear-fractional radicand, possibly several
      roots of it: take n = lcm of the indices): t = ((ax+b)/(cx+d))^(1/n), so x = (d tⁿ − b)/(a − c tⁿ)
      is rational in t; integrate the rational function of t (or a transcendental tower in t if R
      also contains exp/log of such expressions), then substitute back t ↦ the radical.
    * R(x, √(ax² + bx + c)) — Euler substitutions: a > 0: √(…) = t − √a·x; c > 0: √(…) = x t + √c;
      real roots r₁ ≠ r₂: √(…) = t (x − r₁). This gives asin/asinh/acosh-type answers in log/atan form.
      Constants √a, √c may need the ℚ(√d) machinery (QSB) for the coefficients.
    * Anything else with radicals (several independent radicands, √ of a cubic or quartic, radicals
      inside exp/log arguments) stays `RischNotImplemented`, which is honest: e.g. ∫ dx/√(x³+1) is
      elliptic, and deciding elementarity there needs the algebraic Risch algorithm.

    *Implementation sketch.*
    * Detection (front end, before `build_tower`): collect the radicals in the term (`sqrt`, `cbrt`,
      `^` with non-integer rational exponent) and their radicands; classify into one of the rules.
    * Substitution on terms: rebuild the integrand as a function of a fresh variable t with the
      user's `build` / `lift` (a symbolic variable of the same package is needed: create it with the
      package's own constructor, or run the transcendental algorithm on a `Builder` whose `x` is t).
      Alternatively do the substitution inside the exact algebra (parse the radicand into ℚ(x),
      build R(x(t), t)·x'(t) as an element of ℚ(t), integrate there) and only rebuild the answer
      as a term with t replaced by the radical: this avoids needing a symbolic t from the package.
      Prefer the exact route; it keeps verification exact.
    * Back-substitution in the output: t ↦ radical as a term (`mk(b, :sqrt, …)` or `^ (1//n)`).
    * Verification: exact in ℚ(t) (the integral of the transformed integrand), plus the identity
      dx/dt check; the final term is also numerically spot-checked in the tests.
    * Branches: √ is the principal root; answers are valid where the radicand is positive (tests
      should use such points). asin-type answers come out as atan/log forms.
    * Size: moderate, ~200–400 lines. Mostly front-end work; the integration itself is existing code.

    *Tests.* √x, x√x, 1/√x, x²·x^(1/3), x/√(x+1), √(x+1)/x, 1/(x√(x−1)), 1/√(1−x²), 1/√(x²+1),
    √(x²+1), x/√(x²+2x+3), log(√x) (= log(x)/2; refused today because `sqrt` is parsed first),
    exp(√x) (t = √x: 2t eᵗ → elementary), plus refusals: 1/√(x³+1), √x + √(x+1)
    (two radicands — or handle with two substitutions if cheap).

## 4. Lessons learned (bugs we already hit — do not reintroduce)

* `exp` of a sum must **not** be split into separate atoms/generators (`exp(a+b) ≠ exp(a)exp(b)` for the
  algorithm when `a`,`b` diverge and cancel) — fixed in Gruntz.jl; in Risch the tower keeps `exp(u)` whole.
* Hermite/rewrite must substitute **recursively inside** the replacement factor (Gruntz `rewrite`).
* Exponential `rde` bounds: the support of `y` may extend to the cancellation exponent
  `i0 = -f_0/w'` (found via `exp(x+exp(x))`). General cancellation (non-constant `c`) is still missing.
* Package quirks that bit us: SymEngine prints `E` as `exp(1)` and builds `exp(x)` as `E^x`
  (`is_e_const`); sums/products are unordered or merged (tests must not pin the number of generators);
  SimpleExpressions constants are callable (`t()`), `x()` fails; `isexpr` is not available.
* Test pitfalls: antiderivative may be complex-valued (log of a negative) → compare real parts
  (`antiderivative_ok`); finite differences at points where the integrand is real/positive.
  SimpleExpressions evaluates in Float64 and *throws* on log of a negative (SymEngine returns a
  complex value), so test points must also keep every log argument of the *answer* positive — e.g.
  for `log((U+√dV)/(U-√dV))` stay outside the roots of U² - dV² (`1/(x(log²x-2))`: x > e^√2).
  SymEngine's `N` can return a real value with a roundoff-size imaginary part (seen on real-form
  trig answers): test evaluators drop |imag| ≤ 1e-10·|z| only (`sym_eval` in `test_trig.jl`).
* The test files are `include`d into one `Main` by the runner: top-level helper names must be
  unique per file (or identical definitions); only `fd`, `run_tests`, `simple_x`, `sym_x`, `Q` are shared.

## 5. Where `Q` is still hard-wired (after step 3)

Only roles where `Q` really means a rational *number*, plus the ℚ-only stages listed under Progress:
`rational_root_candidates`, `rational_roots`, `rat_sqrt`, `QI`, `QS{D}`, `sqfree_split`, `quad_terms`,
`QuadLog`/`QuadAtan`, `leaf_rational`, `const_int`/`parse_rational` (legacy), `num`, the ℚ methods of
the interface above, `flat`'s output vectors, `solve_relation` (ℚ-linear relations), exponents in
`make_exp`/`make_log`/`parse_tower`, and Stage 5c (`QI0`, `qi`, `ep_*`, `ep_to_term`).

## 6. Message to paste into the new session

> I'm continuing a Julia project at `/Users/jverzani/julia/RischIntegrate`, branch `claude`: an
> implementation of the Risch integration algorithm (Bronstein) that works on any symbolic term type
> implementing TermInterface (`iscall`, `operation`, `arguments`), tested with SimpleExpressions.jl and
> SymEngine.jl; it also loads SpecialFunctions.jl. The single source is `src/Risch.jl`
> (`test/Risch.jl` is a symlink to it). Run tests from `test/` with `julia --project=. test_X.jl` for
> the five files `test_risch`, `test_tower`, `test_integrate`, `test_trig`, `test_constants`; all must
> pass after every step. Please read `REFACTOR_PLAN.md` first: the ground rules (section 0), the
> lessons learned (section 4) and the Progress entries — the most recent are RootSum, R1, R2, R3, T,
> RT, RF, RC, RN, TC, TS, TR, RE, SP, TE, TT, LR, SD, ST, TH, TB, TF, TA, AS, AC, SY, DL, NR, IT, NT, PF (all 2026-10-14), PC, US, WR (2026-10-15).
>
> Next steps (open items): Symbolics.jl support (Num unwrap/rewrap, symbolic constants such as
> sqrt(2): WR entry); precompile workloads in package extensions (PC entry, deferred); radicands
> like U³ after a substitution (US entry).
>
> Ground rules: one plan step at a time; every result self-verified exactly by differentiation;
> `NotElementary` only when the theory decides the case, otherwise `RischNotImplemented`; never
> evaluate constants numerically in answers (numeric sign decisions that only choose a form are
> allowed, see TE). Add a Progress entry for each step. Commit only when I ask, named after the step,
> ending with the Co-Authored-By line. Do not commit or stash my own edits (`README.md`,
> `src/RischIntegrate.jl`, `test/runtests.jl`, `test/test_apostol.jl`, Emacs backup files), and do not
> use `git stash` (I edit files while you work; use a temporary `git worktree` to compare against
> HEAD). Keep scratch files outside the repository. Test pitfalls: helper names must be unique per
> test file; in Julia `exp(1)` and `log(2)` are floats — use `ℯ` (and SymEngine's `log(Basic(2))`)
> for symbolic constants; avoid test integrands with real poles when checking continuity.
