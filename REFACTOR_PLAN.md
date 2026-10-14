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
* **Next: step 9 — the full Risch DE in towers (Bronstein ch. 6, parts of ch. 7).** Outline below (§3, step 9).
* **Then: step 10 — radicals by substitution** (√x, √(ax+b), √(ax²+bx+c)). Outline below (§3, step 10).
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

* **No Julia in the assistant's sandbox** (apt has no candidate; julialang.org is blocked). The user runs the
  tests and pastes errors back. So: small steps, every step ends with all four test files green, and every
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

> I'm continuing a Julia project: `Risch.jl`, an implementation of the Risch integration algorithm
> (Bronstein) that works on any symbolic term type implementing TermInterface (`iscall`, `operation`,
> `arguments`), tested with SimpleExpressions.jl and SymEngine.jl; it also loads SpecialFunctions.jl
> (Ei, Si, Ci, erf, erfi in answers). I attached `REFACTOR_PLAN.md`,
> `Risch.jl` and five passing test files. Please read the plan first, then do **step 9a**
> (full Risch DE in towers: SplitFactor, weak normalisation, normal denominator, SPDE, no-cancellation
> solvers; see §3 step 9). You cannot run Julia; I will run the tests and paste
> errors back. Keep every result self-verified, and do one plan step at a time.
