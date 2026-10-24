# Apostol comparison

RischIntegrate on five term types, SymbolicIntegration.jl's Risch method, and
Giac's own `integrate` for reference, on the 175 apostol problems of
`test/test_apostol.jl`:

| Method | Package | Terms |
|---|---|---|
| `symengine` | RischIntegrate (this package) | SymEngine |
| `expr` | RischIntegrate | Julia `Expr` |
| `simpleexpressions` | RischIntegrate | SimpleExpressions |
| `symbolicutils` | RischIntegrate | SymbolicUtils |
| `giac` | RischIntegrate | [Giac.jl](https://github.com/s-celles/Giac.jl) |
| `si_risch` | [SymbolicIntegration](https://github.com/JuliaSymbolics/SymbolicIntegration.jl), `RischMethod()` | Symbolics |
| `giac_own` | Giac.jl, Giac's `integrate` (for reference) | Giac |

The result is a page, `results/apostol_comparison.html`, with a summary
(counts and times) and a grid with one row per method, one column per
problem. Selecting a problem shows the integrand and each method's answer.

## Running it

RischIntegrate comes from this checkout; everything else from the registry.

```sh
cd benchmark/apostol
julia --project=env_risch -e 'using Pkg; Pkg.instantiate()'   # once, or after changing a package
julia --project=env_si -e 'using Pkg; Pkg.instantiate()'
julia --project=env_giac -e 'using Pkg; Pkg.instantiate()'
julia run_all.jl            # or `julia run_all.jl 60` for a 60 s limit per problem
```

`run_all.jl` runs the methods one after another, so they do not compete for
the CPU, and then builds the page. Open `results/apostol_comparison.html` in a
browser; it is self-contained.

To run or rerun one method, then rebuild the page:

```sh
julia supervise.jl symengine env_risch 120
julia build.jl
```

To pick up a newer registered SymbolicIntegration, run
`julia --project=env_si -e 'using Pkg; Pkg.update()'` first. After adding a
package to an environment's `Project.toml`, run `Pkg.resolve()` in that
environment before `Pkg.instantiate()`.

## How it works

| File | Role |
|---|---|
| `problems.jl` | parses (does not evaluate) the `apostol` vector of `test/test_apostol.jl` into `(integrand, variable)` expressions |
| `worker_*.jl` | one per method: loads the packages, makes the variables, and defines `INTEGRATE`, `SOLVED` and `TOSU` or `EVAL` |
| `core.jl` | shared by the workers: builds each integrand with the worker's variables, integrates, checks, writes a line per problem |
| `supervise.jl` | runs a worker; if one problem takes longer than the limit, kills the process, records a timeout and restarts at the next problem |
| `build.jl`, `template.html` | turn the results into the page |
| `giac_common.jl` | the Giac variables and evaluation, shared by the two Giac workers |
| `env_risch`, `env_giac`, `env_si` | the environments: `env_risch` for RischIntegrate with SymEngine, `Expr`, SimpleExpressions and SymbolicUtils; `env_giac` for Giac.jl (RischIntegrate on its terms, and its own `integrate`); `env_si` for SymbolicIntegration |

Each integrand is built from its expression with the worker's own variables:
`SymEngine.@vars`, `SimpleExpressions.@symbolic_variables`, SymbolicUtils
`@syms x::Real ...`, `Giac.@giac_var`, Symbolics `@variables`. For `expr` the quoted expression is
the integrand, and the answer is built with
`build = (op, args...) -> Expr(:call, nameof(op), args...)` and `lift = identity`.

What is recorded:

- **Solved**: the method returned a result with no unevaluated `∫` and threw
  nothing. RischIntegrate throws when it can not integrate (`NotElementary`,
  `RischNotImplemented`, or a `MethodError` when the term type has no method for
  a special function such as `expinti`); SymbolicIntegration returns an
  unevaluated `∫` instead, and Giac an unevaluated `integrate(...)`.
- **Verified**: a central difference of the answer at `x = 0.31` and `x = 0.57`
  (every other variable given a fixed value) matches the integrand to 1e-4. Real
  values are tried first, then complex ones if the real evaluation fails. An
  answer with RootSums (`IntegralWithRootSums`) is evaluated at real values only.
- **Not checked**: solved, but the answer could not be evaluated numerically.
  Such an answer may be wrong.
- **Differs**: solved, but the derivative does not match: a wrong answer.
- **Times**: each method starts cold in a new process. Integration time is the
  sum of the per-problem times, so it includes compiling; load time is loading
  the packages; wall time is everything, restarts included. Times depend on the
  machine and the Julia version, so compare times only within one run.

How each answer is evaluated: SymEngine with `subs` and `N`; `Expr` by replacing
the variables with numbers and evaluating it (SpecialFunctions and PolyLog
loaded); SimpleExpressions with `replace` and calling the result; Giac with
`substitute` and `evalf`, the values rounded to 12 digits; SymbolicUtils
and Symbolics with `substitute(...; fold = Val(true))`.

`results/results_NAME.tsv` has one line per event, tab separated:

| Line | Fields |
|---|---|
| `L` | load time in seconds, first problem of this process (one line per process start) |
| `V` | package name, version (first process only) |
| `S` | problem, start time (used by `supervise.jl` to enforce the limit) |
| `R` | problem, status (`solved`, `unsolved`, `error`, `timeout`, `crash`), check (`verified`, `unverified`, `wrong`, `none`), seconds, the answer or error (first 400 characters) |
| `D` | the worker finished |
| `T` | wall time in seconds, limit in seconds |

`results/commits.tsv` records the git commit of RischIntegrate (and whether it
had uncommitted changes) when `run_all.jl` ran.

## Adding a method

Write `worker_NAME.jl` following the others. Before `include("core.jl")` it
must set `T_START`, load the packages, and define

- `VAR::Dict{Symbol,Any}`: the variables `x t a b c d z n`
- `INTEGRATE(f, x)`: the method
- `SOLVED(out)::Bool`: did it return an antiderivative?
- for the numeric check, either `TOSU(ex)`, the answer as a SymbolicUtils term,
  or `EVAL(ex, vals)`, the value of `ex` with each variable `v` replaced by the
  number `vals[v]` (a `Dict{Symbol,Number}`), or `nothing` if it does not
  evaluate to a number
- optionally `BUILD(ex)`, the integrand from the problem's expression (by
  default, the expression evaluated with the variables of `VAR`)

Then add it to the loop in `run_all.jl` and to `METHODS` in `build.jl`.

## On GitHub

The `Benchmark` workflow (`.github/workflows/Benchmark.yml`) runs `symbolicutils`, `symengine` and
`expr` on each push to main (and on pull requests that change the benchmark), with a 300 s limit
per problem, then `check.jl` compares the verified problems with the committed results: it fails if a
problem verified there is no longer verified. The new results are kept as the run's artifact; the
committed results and the page are still updated by hand with `run_all.jl`.

```sh
julia check.jl BASELINE_DIR results symbolicutils symengine expr
```

## Updating the page

`build.jl` fills in the numbers, grid, times and versions. The "What stands
out" section is written by hand in `template.html`; check it against the new
results and edit it before publishing.

The package README has a badge comparing the number of apostol problems
verified by `symbolicutils` (RischIntegrate, SymbolicUtils) and `si_risch`
(SymbolicIntegration's `RischMethod`, Symbolics). It links to the page through
rawcdn.githack.com at a commit hash (githack caches each URL permanently, so a
branch name would keep showing the first version it saw). After a run, commit and
push the page, then put that commit's hash in the link.
It is a static badge: after a run that changes these numbers, update
them in the badge URL and its alt text.

## Results so far

Solved (verified) out of 175. Times are on one machine and only comparable within a run.

| Date | Julia | RischIntegrate | symengine | expr | simpleexpressions | symbolicutils | giac | si_risch | giac_own |
|---|---|---|---|---|---|---|---|---|---|
| 2026-10-17 | 1.13.0 | `85c487f` | 150 (147) | 163 (162) | 163 (162) | 162 (161) | 148 (147) | 97 (97) | 172 (171) |
| 2026-10-22 | 1.13.0 | `0d180a6` | 175 (170) | 175 (175) | 174 (174) | 174 (174) | 172 (170) | 97 (97) | 172 (171) |

Notes (2026-10-22 run):

- `symengine`: problems 83 and 84 (∫ asec x, ∫ acsc x) show as differing but are
  right: at the check points 0.31 and 0.57, outside |x| ≥ 1, SymEngine's `asec` is
  the conjugate of Julia's branch. 159, 162 and 172 have special-function terms
  (Ei, ₁F₁) with a parameter, kept as `Expr` terms: solved, not checked.
- `giac`: Giac rewrites `asec(x)` and `acsc(x)` as `acos(1/x)` and `asin(1/x)`,
  which RischIntegrate does not support (83, 84); 172's ₁F₁ needs a symbolic
  `_₁F₁` term (as for `simpleexpressions`).
- `giac_own`: 172 (171) verified; 172's `igamma` evaluates to `undef`.
- The Giac `EVAL` rounds the values to 12 digits before substituting: Giac
  misreads a 17-digit float such as 0.5700099999999999, giving `undef` or a
  wrong value, which made correct answers look wrong or unchecked.
- `symbolicutils` misses problem 165 (∫ eᵗ log(1 + t) dt) with `NotElementary`;
  the other term types solve it.
