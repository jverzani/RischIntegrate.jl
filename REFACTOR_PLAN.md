# Refactor plan: a general constant field under the Risch tower

Read `RISCH_STATUS.md` first, then this file, then `Risch.jl` (≈1785 lines).
Attach to the new session: `Risch.jl`, `Gruntz.jl` (only for reference), `RISCH_STATUS.md`,
this file, and the four test files `test_risch.jl`, `test_tower.jl`, `test_integrate.jl`, `test_trig.jl`.

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
  unless the theory covers the case (see "soundness gap" in the status file).

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

1. **Baseline.** Run all four test files, record results. Do not change anything.
2. **Introduce `C` as an alias only.** `const C = Q`. Rename roles: wherever a `Q` means "constant of the
   field" (coefficient types `QX = UPoly{Q}`, `QXF`, `kconst`, `const_value`, `lq`, `dx`, `integrate_poly`,
   `QI`'s parts stay Q), write `C`. Pure renaming, behaviour identical. Tests green.
3. **Make `C` a type parameter** of `QX`/`QXF` → `CX{C}`, `CXF{C}`, then of `Tower{C}`.
   `Tower(xk, scales)` gets a `C`. Functions get `C` from `T` (or from the argument's type). Still only `C = Q`
   is exercised. This is the big mechanical step (≈40 blocks); do it in groups: (a) algebra + Stage 1
   (`hermite_reduce`, `log_part`, `integrate_rational`), (b) tower construction (`make_exp/log`, `flat`,
   `solve_columns` using `cflat`), (c) integration (`integrate_el`, `residue_logs`, `rde*`), (d) front/back ends.
4. **`is_constant`.** Replace `const_value(f) !== nothing` tests by `is_constant(T, f)` where the meaning is
   "differential constant" (residue criterion in `residue_logs`, `make_log` constant ratio, `rde` cancellation
   test `i0`). Keep `const_value` for rational-only places (exponents). Tests green.
5. **`change_constants` + 5b.** Implement `change_constants`. In `residue_logs`, for an irreducible quadratic
   residue factor: extend `C → C(√d)`, compute `W = gcd(D, A - a·δD)` there, then return the same
   `QuadLog/QuadAtan`-style terms but with tower-element arguments (generalise `QuadLog`/`QuadAtan` to hold
   tower elements `U, V ∈ K[θ]`). Verification: derivative stays inside the base field (as in 5a).
   Add tests: `1/(x*(log(x)^2+2))` → `atan(log(x)/√2)/√2`, `exp(x)/(exp(2x)+... )` etc.
6. **5d constants.** Add the constant registry and the `Cε = Frac{UPoly{Q}}` field. Then
   `exp(x+1)` = `ε·exp(x)`, `log(2x)` = `log 2 + log x`, `sin(x+1)`. Update `make_exp/make_log/ep_linear`
   (the "nonzero constant" `RischNotImplemented`s), and the output builder (constants `exp(1)`, `log(2)` via
   `deferred_call`). Tests: `exp(x)+exp(x+1)`, `log(x)+log(2x)`, `∫exp(x+1)`, `sin(x+1)*x`.
7. **5c-ii.** With `C = QI`: general trig through `exp(ix)`, real-form output
   (`F = (v + conj(v))/2`, `θ^k + θ^-k → 2cos kx`, logs with complex residues → `atan`/`log` of norms).
   Needs `rational_roots` over `QI` (or restrict to residues in `ℚ(i)`) and `flat` over `QI`.
8. **Soundness work (optional, high value):** general cancellation in `rde` (Bronstein ch. 6, parametric
   logarithmic derivative), normal denominators in tower RDEs (6.2–6.3), limited integration (ch. 7).

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

## 5. Where `Q` is hard-wired today (block start line, name, #mentions)

```
 46 Q = Rational{BigInt}        290 rational_root_candidates   303 rational_roots     321 rat_sqrt
328 QI (+ toQI 348)             353 QX / 354 QXF               356-358 dx, kconst     360 integrate_poly
394 QuadLog  400 QuadAtan       407 RationalIntegral           417 QS{D} (+ ops)      452 quad_terms
486 log_part                    549 integrate_rational         558 derivative_of      578 check_result
590 leaf_rational               616 const_int                  624 parse_rational (legacy, unused by risch_integrate)
664 num   720 poly_term   735 frac_term                         (output; coefficients are Q)
792 Tower   812 lq   815-816 const_value   822 D   839/845 flat   854 solve_columns   884 solve_relation
898 make_exp   940 make_log   1005 parse_tower
1163 rde_base (ℚ(x) only)   1260 rde
1368 ElemIntegral   1375 residue_logs   1412 integrate_log_poly   1452 integrate_el   1540 check_tower
1582-1735 Stage 5c (QI0, qi, ep_*, parse_ep, ep_integrate, ep_to_term)   1759 risch_integrate
```

## 6. Message to paste into the new session

> I'm continuing a Julia project: `Risch.jl`, an implementation of the Risch integration algorithm
> (Bronstein) that works on any symbolic term type implementing TermInterface (`iscall`, `operation`,
> `arguments`), tested with SimpleExpressions.jl and SymEngine.jl. I attached `RISCH_STATUS.md`,
> `REFACTOR_PLAN.md`, `Risch.jl`, `Gruntz.jl` and four passing test files. Please read the status and
> plan files first, then do **step 2** of the refactor plan (introduce the constant-field type `C` as an
> alias of `Q` and rename the places where `Q` means "constant of the differential field"), changing
> behaviour nowhere. You cannot run Julia; I will run the tests and paste errors back. Keep every result
> self-verified, and do one plan step at a time.
