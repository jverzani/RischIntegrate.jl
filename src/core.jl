#     Risch
#
# Symbolic integration following Bronstein, *Symbolic Integration I: Transcendental
# Functions*, for any symbolic term type that implements the TermInterface.jl
# methods `iscall`, `operation` and `arguments` (SimpleExpressions.jl, SymEngine.jl,
# `Expr`, ...). Nothing else is required: all algebra is done by this module's own
# exact, dependency-free polynomial / rational-function types, and results are
# rebuilt by calling operations as functions (same `build` / `lift` conventions as
# `Gruntz.jl`).
#
#     risch_integrate(f, x; build = nothing, lift = nothing, verify = true)
#
# # Roadmap (each stage is usable on its own)
#
# * **Stage 1 (this file)** – exact algebra and rational functions in `x` over ℚ:
#     `UPoly{T}` (dense univariate polynomials over any field `T`), `Frac{P}`
#     (normalised fraction field), gcd / extended gcd / squarefree factorisation /
#     resultant, differential-field derivation, **Hermite reduction** (Bronstein 2.2)
#     and the **Rothstein–Trager** log part (rational residues, and complex-conjugate
#     residues with rational real/imaginary parts -> `atan`).
#     Every answer is *verified by differentiation* inside the exact field.
# * **Stage 2 (done)** – front end for towers: recognise `exp`, `log` (and rewrite
#     `sin, cos, tan, sinh, ...` through `exp`) and build the monomial tower
#     ℚ(x)(θ₁)…(θₙ) with its derivation (Bronstein ch. 5.1, structure theorems 9.x
#     for tower validity). Output conversion back to terms.
# * **Stage 3 (log towers complete; exp towers up to the Risch DE)** – integration in a monomial extension: Hermite
#     reduction with a general derivation (already written to take `δ`), the
#     polynomial reduction (5.8/5.9 for log, 5.10/5.11 for exp), residue criterion
#     (5.6-5.7) for the log part.
# * **Stage 4 (done, restricted shapes over towers)** – Risch differential equation solvers (ch. 6: weak normalisation,
#     SPDE, base case ℚ(x), exp/log cases) and limited integration (ch. 7).
# * **Stage 5** – parametric RDE / structure theorem, non-elementary detection
#     ("this integral is not elementary"), irrational residues (algebraic constants,
#     `RootSum`), real forms for trigonometric input.
#
# Stage 1 deliberately raises `RischNotImplemented` for anything outside its scope.
#
# Non-elementary integrals that can be written with SpecialFunctions.jl (Ei, Si, Ci, erf, erfi;
# li(x) as Ei(log x)) are returned that way, verified like every other answer; `NotElementary`
# is raised when the integral is proved non-elementary and no such form was found.

const Q = Rational{BigInt}

# Role separation (refactor, step 2).
#   Q : exact rational NUMBERS: exponents, multiplicities, degrees, coefficients of
#       ℚ-linear relations between generators, output formatting.
#   C : CONSTANTS of the differential field, i.e. the coefficients of the base polynomials
#       C(x). Today C === Q; later steps make it a type parameter (ℚ(√d), ℚ(i), ℚ(e), ...).
const C = Q
cfrom(q::Q) = q                 # embedding ℚ -> C
czero() = zero(C)
cone() = one(C)

"""
    RischError

An internal error, e.g. an answer that failed its own check by differentiation. It indicates a bug.
"""
struct RischError <: Exception
    msg::String
end
"""
    RischNotImplemented

The integrand lies outside the cases implemented: no answer, and no decision whether the integral
is elementary.
"""
struct RischNotImplemented <: Exception
    msg::String
end
Base.showerror(io::IO, e::RischError) = print(io, "RischError: ", e.msg)
Base.showerror(io::IO, e::RischNotImplemented) = print(io, "RischNotImplemented: ", e.msg)

# Raised when the algorithm *decides* that the integral has no elementary
# antiderivative (within the cases of the Risch algorithm implemented so far).
"""
    NotElementary

The integral was proved to have no elementary antiderivative (and no form with the special
functions used by the package was found).
"""
struct NotElementary <: Exception
    msg::String
end
Base.showerror(io::IO, e::NotElementary) = print(io, "NotElementary: no elementary antiderivative: ", e.msg)
