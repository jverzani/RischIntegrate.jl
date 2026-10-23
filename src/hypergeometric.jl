# ---------------------------------------------------------------------------
# SI2 phase 6, H1: non-elementary remainders with binomial radicands as ₂F₁ terms
#
# After Hermite reduction (and the log part) a non-elementary integral leaves a residue-free remainder
# Σₖ pₖ xᵏ bᵠ with b = α + βxⁿ (one radicand). For α > 0 and m ≥ 0:
#   ∫ xᵐ(α + βxⁿ)ᵠ dx = α^q x^(m+1)/(m+1) · ₂F₁(-q, (m+1)/n; (m+1)/n + 1; -βxⁿ/α)
# (differentiate the series termwise; Rubi writes α^q as bᵠ/(1 + βxⁿ/α)ᵠ). The argument -βxⁿ/α < 1 where
# b > 0, so the principal branch is used. The terms are kept apart from the symbolic answer and evaluated
# numerically (as RootSums are), in an `IntegralWithRootSums`. HYP_ANSWERS[] = false restores
# `NotElementary` for these integrals.
# ---------------------------------------------------------------------------
using HypergeometricFunctions: _₂F₁

const HYP_ANSWERS = Ref(true)

"""
    HypTerm

`c α^q x^(m+1)/(m+1) ₂F₁(-q, (m+1)/n; (m+1)/n + 1; -βxⁿ/α)`, an antiderivative of `c xᵐ (α + βxⁿ)^q`.
Callable through the `IntegralWithRootSums` it belongs to.
"""
struct HypTerm
    c::Q
    m::Int
    n::Int
    α::Q
    β::Q
    q::Q
    var::String
end

function Base.show(io::IO, h::HypTerm)
    a, c = Q(h.m + 1, h.n), Q(h.m + 1, h.n) + 1
    fr(r) = isone(denominator(r)) ? string(numerator(r)) : "$(numerator(r))/$(denominator(r))"
    k = h.c / (h.m + 1)
    z = -h.β / h.α
    pw(e) = e == 1 ? h.var : "$(h.var)^$e"
    isone(k) || print(io, k == -1 ? "-" : "($(fr(k)))*")
    isone(h.α) || print(io, "($(fr(h.α)))^($(fr(h.q)))*")
    print(io, pw(h.m + 1), "*₂F₁(", fr(-h.q), ", ", fr(a), "; ", fr(c), "; ",
          isone(z) ? "" : z == -1 ? "-" : "($(fr(z)))*", pw(h.n), ")")
end

function hyp_value(h::HypTerm, a::Number)
    x = complex(float(a))
    z = -Float64(h.β / h.α) * x^h.n
    Float64(h.c) * Float64(h.α)^Float64(h.q) * x^(h.m + 1) / (h.m + 1) *
        _₂F₁(-Float64(h.q), (h.m + 1) / h.n, (h.m + 1) / h.n + 1, z)
end
rs_value(h::HypTerm, xk::String, a) = hyp_value(h, a)
rs_value_continuous(h::HypTerm, xk::String, a::Real) = hyp_value(h, a)
depends_on(h::HypTerm, yk::String) = h.var == yk

# Σₖ pₖ xᵏ bᵠ as HypTerms when b = α + βxⁿ with α > 0, else nothing
function hyp_binomial_terms(b::QX, q::Q, P::QX, xk::String)
    HYP_ANSWERS[] || return nothing
    nz = [i for i in eachindex(b.c) if !iszero(b.c[i])]
    (length(nz) == 2 && nz[1] == 1 && b.c[1] > 0) || return nothing
    n = nz[2] - 1
    Any[HypTerm(P.c[k + 1], k, n, b.c[1], b.c[n + 1], q, xk) for k in 0:degree(P) if !iszero(P.c[k + 1])]
end
