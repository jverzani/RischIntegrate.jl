"""
    Risch

Symbolic integration following Bronstein, *Symbolic Integration I: Transcendental
Functions*, for any symbolic term type that implements the TermInterface.jl
methods `iscall`, `operation` and `arguments` (SimpleExpressions.jl, SymEngine.jl,
`Expr`, ...). Nothing else is required: all algebra is done by this module's own
exact, dependency-free polynomial / rational-function types, and results are
rebuilt by calling operations as functions (same `build` / `lift` conventions as
`Gruntz.jl`).

    risch_integrate(f, x; build = nothing, lift = nothing, verify = true)

# Roadmap (each stage is usable on its own)

* **Stage 1 (this file)** – exact algebra and rational functions in `x` over ℚ:
    `UPoly{T}` (dense univariate polynomials over any field `T`), `Frac{P}`
    (normalised fraction field), gcd / extended gcd / squarefree factorisation /
    resultant, differential-field derivation, **Hermite reduction** (Bronstein 2.2)
    and the **Rothstein–Trager** log part (rational residues, and complex-conjugate
    residues with rational real/imaginary parts -> `atan`).
    Every answer is *verified by differentiation* inside the exact field.
* **Stage 2 (done)** – front end for towers: recognise `exp`, `log` (and rewrite
    `sin, cos, tan, sinh, ...` through `exp`) and build the monomial tower
    ℚ(x)(θ₁)…(θₙ) with its derivation (Bronstein ch. 5.1, structure theorems 9.x
    for tower validity). Output conversion back to terms.
* **Stage 3 (log towers complete; exp towers up to the Risch DE)** – integration in a monomial extension: Hermite
    reduction with a general derivation (already written to take `δ`), the
    polynomial reduction (5.8/5.9 for log, 5.10/5.11 for exp), residue criterion
    (5.6-5.7) for the log part.
* **Stage 4 (done, restricted shapes over towers)** – Risch differential equation solvers (ch. 6: weak normalisation,
    SPDE, base case ℚ(x), exp/log cases) and limited integration (ch. 7).
* **Stage 5** – parametric RDE / structure theorem, non-elementary detection
    ("this integral is not elementary"), irrational residues (algebraic constants,
    `RootSum`), real forms for trigonometric input.

Stage 1 deliberately raises `RischNotImplemented` for anything outside its scope.

Non-elementary integrals that can be written with SpecialFunctions.jl (Ei, Si, Ci, erf, erfi;
li(x) as Ei(log x)) are returned that way, verified like every other answer; `NotElementary`
is raised when the integral is proved non-elementary and no such form was found.
"""
module Risch

using TermInterface: iscall, operation, arguments
using SpecialFunctions: expinti, sinint, cosint, erf, erfi

export risch_integrate, integrate_rational, tower_derivative, RischError, RischNotImplemented,
       NotElementary, RootSum, TermRootSum, IntegralWithRootSums

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

struct RischError <: Exception
    msg::String
end
struct RischNotImplemented <: Exception
    msg::String
end
Base.showerror(io::IO, e::RischError) = print(io, "RischError: ", e.msg)
Base.showerror(io::IO, e::RischNotImplemented) = print(io, "RischNotImplemented: ", e.msg)

# Raised when the algorithm *decides* that the integral has no elementary
# antiderivative (within the cases of the Risch algorithm implemented so far).
struct NotElementary <: Exception
    msg::String
end
Base.showerror(io::IO, e::NotElementary) = print(io, "NotElementary: no elementary antiderivative: ", e.msg)

# ---------------------------------------------------------------------------
# Dense univariate polynomials over a field T (coefficients low -> high)
# ---------------------------------------------------------------------------
struct UPoly{T}
    c::Vector{T}
    function UPoly{T}(c::Vector{T}) where {T}
        v = copy(c)
        while !isempty(v) && iszero(v[end])
            pop!(v)
        end
        new{T}(v)
    end
end

Base.zero(::Type{UPoly{T}}) where {T} = UPoly{T}(T[])
Base.one(::Type{UPoly{T}}) where {T} = UPoly{T}(T[one(T)])
Base.zero(p::UPoly) = zero(typeof(p))
Base.one(p::UPoly) = one(typeof(p))
Base.iszero(p::UPoly) = isempty(p.c)
Base.isone(p::UPoly) = length(p.c) == 1 && isone(p.c[1])
Base.:(==)(p::UPoly, q::UPoly) = p.c == q.c
Base.hash(p::UPoly, h::UInt) = hash(p.c, h)

degree(p::UPoly) = length(p.c) - 1          # -1 for the zero polynomial
lc(p::UPoly) = p.c[end]
xpoly(::Type{T}) where {T} = UPoly{T}(T[zero(T), one(T)])

function Base.:+(p::UPoly{T}, q::UPoly{T}) where {T}
    n = max(length(p.c), length(q.c))
    r = Vector{T}(undef, n)
    for i in 1:n
        r[i] = (i <= length(p.c) ? p.c[i] : zero(T)) + (i <= length(q.c) ? q.c[i] : zero(T))
    end
    UPoly{T}(r)
end
Base.:-(p::UPoly{T}) where {T} = UPoly{T}(T[-a for a in p.c])
Base.:-(p::UPoly{T}, q::UPoly{T}) where {T} = p + (-q)
function Base.:*(p::UPoly{T}, q::UPoly{T}) where {T}
    (iszero(p) || iszero(q)) && return zero(p)
    r = fill(zero(T), length(p.c) + length(q.c) - 1)
    for i in eachindex(p.c), j in eachindex(q.c)
        r[i + j - 1] += p.c[i] * q.c[j]
    end
    UPoly{T}(r)
end
Base.:*(n::Integer, p::UPoly{T}) where {T} = UPoly{T}(T[n * c for c in p.c])
function Base.:^(p::UPoly, n::Integer)
    n < 0 && throw(DomainError(n, "negative power of a polynomial"))
    r, b = one(p), p
    while n > 0
        isodd(n) && (r = r * b)
        n >>= 1
        n > 0 && (b = b * b)
    end
    r
end

scale(a::T, p::UPoly{T}) where {T} = UPoly{T}(T[a * c for c in p.c])
scale_div(p::UPoly{T}, a::T) where {T} = UPoly{T}(T[c / a for c in p.c])
divint(p::UPoly{T}, j::Integer) where {T} = scale_div(p, j * one(T))
monic(p::UPoly) = iszero(p) ? p : scale_div(p, lc(p))

function Base.divrem(a::UPoly{T}, b::UPoly{T}) where {T}
    iszero(b) && throw(DivideError())
    db, lb = degree(b), lc(b)
    n = length(a.c) - length(b.c) + 1
    n <= 0 && return (zero(a), a)
    r = copy(a.c)
    q = fill(zero(T), n)
    for k in n:-1:1
        coef = r[k + db] / lb
        q[k] = coef
        iszero(coef) && continue
        for j in 0:db
            r[k + j] -= coef * b.c[j + 1]
        end
    end
    (UPoly{T}(q), UPoly{T}(r[1:db]))
end
quo(a::UPoly{T}, b::UPoly{T}) where {T} = divrem(a, b)[1]
Base.rem(a::UPoly{T}, b::UPoly{T}) where {T} = divrem(a, b)[2]

# formal derivative d/dθ
deriv(p::UPoly{T}) where {T} = UPoly{T}(T[i * p.c[i + 1] for i in 1:degree(p)])

function peval(p::UPoly{T}, a::T) where {T}
    r = zero(T)
    for i in length(p.c):-1:1
        r = r * a + p.c[i]
    end
    r
end

# Euclid with monic remainders (same gcd; over function fields such as ℚ(e) this keeps the
# coefficients from swelling)
function Base.gcd(a::UPoly{T}, b::UPoly{T}) where {T}
    while !iszero(b)
        a, b = b, monic(rem(a, b))
    end
    monic(a)
end

# s*a + t*b = g, with g monic. Remainders are made monic as they appear (s, t scaled along, so
# s*a + t*b = r stays true): the same result, without coefficient swell over function fields.
function gcdex(a::UPoly{T}, b::UPoly{T}) where {T}
    P = typeof(a)
    r0, r1 = a, b
    s0, s1 = one(P), zero(P)
    t0, t1 = zero(P), one(P)
    while !iszero(r1)
        q, r = divrem(r0, r1)
        s2, t2 = s0 - q * s1, t0 - q * t1
        if !iszero(r)
            l = lc(r)
            r, s2, t2 = scale_div(r, l), scale_div(s2, l), scale_div(t2, l)
        end
        r0, r1 = r1, r
        s0, s1 = s1, s2
        t0, t1 = t1, t2
    end
    iszero(r0) && return (s0, t0, r0)
    l = lc(r0)
    (scale_div(s0, l), scale_div(t0, l), scale_div(r0, l))
end

# Yun's squarefree factorisation: p = lc * prod a_i^i, a_i monic, squarefree, coprime
function squarefree(p::P) where {P<:UPoly}
    out = Pair{P,Int}[]
    degree(p) <= 0 && return out
    p = monic(p)
    dp = deriv(p)
    g = gcd(p, dp)
    b = quo(p, g)
    c = quo(dp, g)
    d = c - deriv(b)
    i = 1
    while degree(b) > 0
        a = gcd(b, d)
        degree(a) > 0 && push!(out, a => i)
        b = quo(b, a)
        c = quo(d, a)
        d = c - deriv(b)
        i += 1
    end
    out
end

# Resultant over a field by the Euclidean recurrence
function resultant(a::UPoly{T}, b::UPoly{T}) where {T}
    (iszero(a) || iszero(b)) && return zero(T)
    da, db = degree(a), degree(b)
    db == 0 && return lc(b)^da
    da == 0 && return lc(a)^db
    r = rem(a, b)
    iszero(r) && return zero(T)
    dr = degree(r)
    s = iseven(da * db) ? 1 : -1
    s * (lc(b)^(da - dr) * resultant(b, r))
end

# ---------------------------------------------------------------------------
# Fraction field of a polynomial ring over a field (normalised: gcd 1, monic den)
# ---------------------------------------------------------------------------
struct Frac{P}
    num::P
    den::P
end

function frac(n::P, d::P) where {P<:UPoly}
    iszero(d) && throw(DivideError())
    iszero(n) && return Frac{P}(zero(P), one(P))
    g = gcd(n, d)
    if degree(g) > 0
        n, d = quo(n, g), quo(d, g)
    end
    l = lc(d)
    isone(l) ? Frac{P}(n, d) : Frac{P}(scale_div(n, l), scale_div(d, l))
end
frac(n::P) where {P<:UPoly} = Frac{P}(n, one(P))

Base.zero(::Type{Frac{P}}) where {P} = Frac{P}(zero(P), one(P))
Base.one(::Type{Frac{P}}) where {P} = Frac{P}(one(P), one(P))
Base.zero(f::Frac) = zero(typeof(f))
Base.one(f::Frac) = one(typeof(f))
Base.iszero(f::Frac) = iszero(f.num)
Base.isone(f::Frac) = isone(f.num) && isone(f.den)
Base.:(==)(f::Frac, g::Frac) = f.num == g.num && f.den == g.den
Base.hash(f::Frac, h::UInt) = hash(f.den, hash(f.num, h))
Base.:-(f::Frac{P}) where {P} = Frac{P}(-f.num, f.den)
Base.:+(f::Frac{P}, g::Frac{P}) where {P} = frac(f.num * g.den + g.num * f.den, f.den * g.den)
Base.:-(f::Frac{P}, g::Frac{P}) where {P} = f + (-g)
Base.:*(f::Frac{P}, g::Frac{P}) where {P} = frac(f.num * g.num, f.den * g.den)
Base.inv(f::Frac{P}) where {P} = frac(f.den, f.num)
Base.:/(f::Frac{P}, g::Frac{P}) where {P} = f * inv(g)
Base.:*(n::Integer, f::Frac{P}) where {P} = frac(n * f.num, f.den)
Base.:*(f::Frac, n::Integer) = n * f
function Base.:^(f::Frac, n::Integer)
    n < 0 && return inv(f)^(-n)
    r, b = one(f), f
    while n > 0
        isodd(n) && (r = r * b)
        n >>= 1
        n > 0 && (b = b * b)
    end
    r
end

# ---------------------------------------------------------------------------
# Small helpers: integer factoring, rational roots, Gaussian rationals
# ---------------------------------------------------------------------------
function factorint(n::BigInt)
    f = Pair{BigInt,Int}[]
    p = big(2)
    while p * p <= n && p < 1_000_000
        k = 0
        while n % p == 0
            n ÷= p
            k += 1
        end
        k > 0 && push!(f, p => k)
        p += (p == 2 ? 1 : 2)
    end
    n > 1 && push!(f, n => 1)
    f
end

function divisors(n::BigInt)
    ds = BigInt[1]
    for (p, k) in factorint(n)
        ds = BigInt[d * p^e for d in ds for e in 0:k]
    end
    ds
end

function rational_root_candidates(p::UPoly{Q})
    c = p.c
    l = reduce(lcm, denominator.(c))
    ic = BigInt[numerator(x * l) for x in c]
    out = Set{Q}()
    for a in divisors(abs(ic[1])), b in divisors(abs(ic[end]))
        push!(out, Q(a) // Q(b))
        push!(out, -(Q(a) // Q(b)))
    end
    out
end

# distinct rational roots of p
function rational_roots(p::UPoly{Q})
    roots = Q[]
    iszero(p) && return roots
    c = copy(p.c)
    if iszero(c[1])
        push!(roots, Q(0))
        while !isempty(c) && iszero(c[1])
            popfirst!(c)
        end
    end
    length(c) <= 1 && return roots
    q = UPoly{Q}(c)
    for r in rational_root_candidates(q)
        iszero(peval(q, r)) && push!(roots, r)
    end
    roots
end

# distinct roots in the constant field C of a polynomial over C. Contract: the result may be
# INCOMPLETE (a field may only find some of its roots, see ℚ(√d)); every caller divides out the
# roots found and treats a leftover factor of positive degree as "not handled"
# (RischNotImplemented / `unresolved`), never as "no roots". For ℚ the result is complete.
constant_roots(p::UPoly{Q}) = rational_roots(p)
constant_roots(p::UPoly) = throw(RischNotImplemented(
    "root finding in this constant field is not implemented"))

function rat_sqrt(a::Q)
    a < 0 && return nothing
    n, d = isqrt(numerator(a)), isqrt(denominator(a))
    (n^2 == numerator(a) && d^2 == denominator(a)) ? Q(n) // Q(d) : nothing
end

# --- factorisation in ℚ[z] (residue polynomials) ------------------------------------
# Big prime method: the primitive integer form f of a squarefree polynomial is factored modulo
# a prime p > 2·|lc f|·B, B = 2ⁿ‖f‖₂ (Mignotte: a bound on the coefficients of any factor), by
# Cantor–Zassenhaus; the factors over ℤ are the products of modular ones (times lc f, in the
# symmetric range), found by trying subsets in order of size. Every factor returned divides f
# exactly; only their irreducibility rests on p being prime (Miller–Rabin), and callers never
# depend on it for correctness (a reducible factor is merely handled less well).

# polynomials over 𝔽ₚ: Vector{BigInt}, low -> high, entries in [0, p), no top zeros
function fp_norm(a::Vector{BigInt}, p::BigInt)
    b = BigInt[mod(c, p) for c in a]
    while !isempty(b) && iszero(b[end])
        pop!(b)
    end
    b
end
fp_sub(a, b, p) = fp_norm(BigInt[(i <= length(a) ? a[i] : big(0)) - (i <= length(b) ? b[i] : big(0))
                                 for i in 1:max(length(a), length(b))], p)
function fp_mul(a, b, p)
    (isempty(a) || isempty(b)) && return BigInt[]
    c = zeros(BigInt, length(a) + length(b) - 1)
    for i in eachindex(a), j in eachindex(b)
        c[i + j - 1] += a[i] * b[j]
    end
    fp_norm(c, p)
end
function fp_divrem(a, b, p)
    q = zeros(BigInt, max(length(a) - length(b) + 1, 0))
    li = invmod(b[end], p)
    while length(a) >= length(b)
        c = mod(a[end] * li, p)
        s = length(a) - length(b)
        q[s + 1] = c
        a = copy(a)
        for k in eachindex(b)
            a[s + k] -= c * b[k]
        end
        a = fp_norm(a, p)
    end
    fp_norm(q, p), a
end
fp_monic(a, p) = isempty(a) ? a : fp_norm(a .* invmod(a[end], p), p)
function fp_gcd(a, b, p)
    while !isempty(b)
        a, b = b, fp_divrem(a, b, p)[2]
    end
    fp_monic(a, p)
end
function fp_powmod(a, e::BigInt, f, p)
    r = BigInt[1]
    a = fp_divrem(a, f, p)[2]
    while e > 0
        isodd(e) && (r = fp_divrem(fp_mul(r, a, p), f, p)[2])
        e >>= 1
        e > 0 && (a = fp_divrem(fp_mul(a, a, p), f, p)[2])
    end
    r
end

function is_probable_prime(n::BigInt)
    n < 2 && return false
    small = (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53)
    for q in small
        n % q == 0 && return n == q
    end
    d, s = n - 1, 0
    while iseven(d)
        d >>= 1
        s += 1
    end
    for a in small
        x = powermod(big(a), d, n)
        (x == 1 || x == n - 1) && continue
        composite = true
        for _ in 1:(s - 1)
            x = mod(x * x, n)
            if x == n - 1
                composite = false
                break
            end
        end
        composite && return false
    end
    true
end

# distinct-degree factorisation of a monic squarefree f: [(g, d)], g the product of the
# irreducible factors of degree d
function fp_ddf(f, p)
    out = Tuple{Vector{BigInt},Int}[]
    xp = BigInt[0, 1]
    w = xp
    d = 0
    while length(f) - 1 >= 2 * (d + 1)
        d += 1
        w = fp_powmod(w, p, f, p)                       # x^(p^d) mod f
        g = fp_gcd(f, fp_sub(w, xp, p), p)
        if length(g) > 1
            push!(out, (g, d))
            f = fp_divrem(f, g, p)[1]
            w = fp_divrem(w, f, p)[2]
        end
    end
    length(f) > 1 && push!(out, (f, length(f) - 1))
    out
end

# equal-degree splitting (p odd) of a monic g whose irreducible factors all have degree d;
# the "random" elements come from a fixed LCG, so results are reproducible
function fp_edf(g, d::Int, p, seed::Ref{BigInt})
    n = length(g) - 1
    n == d && return [g]
    e = (p^d - 1) ÷ 2
    while true
        a = BigInt[]
        for _ in 1:n
            seed[] = mod(seed[] * 6364136223846793005 + 1442695040888963407, big(2)^128)
            push!(a, mod(seed[] >> 32, p))
        end
        a = fp_norm(a, p)
        length(a) <= 1 && continue
        c = fp_gcd(g, fp_sub(fp_powmod(a, e, g, p), BigInt[1], p), p)
        1 < length(c) < length(g) &&
            return vcat(fp_edf(c, d, p, seed), fp_edf(fp_divrem(g, c, p)[1], d, p, seed))
    end
end

combos(r::UnitRange{Int}, k::Int) =
    k == 0 ? [Int[]] : [vcat(i, c) for i in r for c in combos((i + 1):last(r), k - 1)]

# monic irreducible factors of a squarefree f ∈ ℚ[z] (product = monic(f))
function factor_Q(f::UPoly{Q})
    degree(f) <= 1 && return [monic(f)]
    l = reduce(lcm, denominator.(f.c))
    F = BigInt[numerator(c * l) for c in f.c]
    F = F .÷ reduce(gcd, F)
    n = length(F) - 1
    p = 2 * abs(F[end]) * big(2)^n * (isqrt(sum(c^2 for c in F)) + 1) + 1
    while true
        p += 1
        is_probable_prime(p) || continue
        fm = fp_monic(fp_norm(F, p), p)
        dfm = fp_norm(BigInt[k * fm[k + 1] for k in 1:n], p)
        length(fp_gcd(fm, dfm, p)) == 1 && break        # squarefree mod p
    end
    seed = Ref(big(20240611))
    mods = Vector{BigInt}[]
    for (g, d) in fp_ddf(fp_monic(fp_norm(F, p), p), p)
        append!(mods, fp_edf(g, d, p, seed))
    end
    out = UPoly{Q}[]
    k = 1
    while 2k <= length(mods)
        hit = nothing
        for S in combos(1:length(mods), k)
            g = BigInt[mod(F[end], p)]
            for i in S
                g = fp_mul(g, mods[i], p)
            end
            g = BigInt[c > p ÷ 2 ? c - p : c for c in g]
            g = g .÷ reduce(gcd, g)
            qq, rr = divrem(UPoly{Q}(Q.(F)), UPoly{Q}(Q.(g)))
            if iszero(rr)
                hit = (S, g, qq)
                break
            end
        end
        if hit === nothing
            k += 1
        else
            S, g, qq = hit
            push!(out, monic(UPoly{Q}(Q.(g))))
            all(c -> isone(denominator(c)), qq.c) || throw(RischError("factor_Q: non-integral cofactor"))
            F = BigInt[numerator(c) for c in qq.c]
            mods = mods[setdiff(1:length(mods), S)]
        end
    end
    push!(out, monic(UPoly{Q}(Q.(F))))
    out
end

# Gaussian rationals Q(i): the field in which complex residues are handled
struct QI
    re::Q
    im::Q
end
Base.zero(::Type{QI}) = QI(Q(0), Q(0))
Base.one(::Type{QI}) = QI(Q(1), Q(0))
Base.iszero(a::QI) = iszero(a.re) && iszero(a.im)
Base.isone(a::QI) = isone(a.re) && iszero(a.im)
Base.:(==)(a::QI, b::QI) = a.re == b.re && a.im == b.im
Base.:+(a::QI, b::QI) = QI(a.re + b.re, a.im + b.im)
Base.:-(a::QI, b::QI) = QI(a.re - b.re, a.im - b.im)
Base.:-(a::QI) = QI(-a.re, -a.im)
Base.:*(a::QI, b::QI) = QI(a.re * b.re - a.im * b.im, a.re * b.im + a.im * b.re)
Base.:*(n::Integer, a::QI) = QI(n * a.re, n * a.im)
Base.hash(a::QI, h::UInt) = hash(a.im, hash(a.re, h))
function Base.inv(a::QI)
    n = a.re^2 + a.im^2
    QI(a.re / n, -a.im / n)
end
Base.:/(a::QI, b::QI) = a * inv(b)
toQI(p::UPoly{Q}) = UPoly{QI}(QI[QI(c, Q(0)) for c in p.c])

# ---------------------------------------------------------------------------
# Differential structure of ℚ(x): d/dx
# ---------------------------------------------------------------------------
const CX = UPoly{C}              # C[x]
const CXF = Frac{CX}             # C(x), the base field K_0
const QX = CX                    # legacy names, kept for the tests and external callers
const QXF = CXF

# d/dx on the base level (valid ONLY for elements of C(x): at higher levels use D(T, i, f))
dx(p::UPoly) = deriv(p)
dx(f::Frac{<:UPoly}) = frac(deriv(f.num) * f.den - f.num * deriv(f.den), f.den * f.den)
kconst(c::T) where {T} = frac(UPoly{T}(T[c]))       # constant c as an element of C(x)

function integrate_poly(p::UPoly{T}) where {T}
    iszero(p) && return p
    UPoly{T}(T[i == 1 ? zero(T) : p.c[i - 1] / ((i - 1) * one(T)) for i in 1:(length(p.c) + 1)])
end

# ---------------------------------------------------------------------------
# Hermite reduction (Bronstein, Alg. 2.2 / 5.x), for a derivation δ on K[θ]:
#   A/D  =  Q  +  (g)'  +  R/Dsf
# with Q polynomial, g the rational part, Dsf squarefree. Returns (g, Q, R, Dsf).
# ---------------------------------------------------------------------------
function hermite_reduce(δ, A::P, D::P) where {P<:UPoly}
    Qp, R = divrem(A, D)
    g = zero(Frac{P})
    for (V, m) in squarefree(D)
        m >= 2 || continue
        for j in (m - 1):-1:1
            Dstar = quo(D, V^(j + 1))
            dV = δ(V)
            s, _, gg = gcdex(Dstar * dV, V)
            isone(gg) || throw(RischError("Hermite reduction: gcd(D*V', V) != 1"))
            B = rem(s * R, V)
            Cq = quo(R - B * Dstar * dV, V)
            g = g + frac(-B, j * V^j)
            R = Cq + divint(δ(B), j)
            D = quo(D, V)
        end
    end
    g, Qp, R, D
end

# ---------------------------------------------------------------------------
# Rothstein–Trager log part for R/D, D squarefree monic, deg R < deg D, over ℚ
# ---------------------------------------------------------------------------
# Stage 5a: terms with quadratic-irrational constants (residues in ℚ(√d), d squarefree)
struct QuadLog                  # β√d · log((U + √d V)/(U - √d V)),  d > 1
    β::Q
    d::Int
    U::CX
    V::CX
end
struct QuadAtan                 # c√e · atan(√e u)  (inverted = false)  or  c√e · atan(u/√e)  (true)
    c::Q
    e::Int
    u::CXF
    inverted::Bool
end

struct RationalIntegral{C}
    rational::Frac{UPoly{C}}               # rational (non-log) part
    logs::Vector{Tuple{C,UPoly{C}}}        # c * log(w)
    atans::Vector{Tuple{C,Frac{UPoly{C}}}} # c * atan(u)
    unresolved::Vector{Any}                # (residue polynomial, R, D) not handled yet
    quads::Vector{Any}                     # QuadLog / QuadAtan (C = ℚ only)
end
RationalIntegral(r, l, a, u) = RationalIntegral(r, l, a, u, Any[])

# the field B(√D), D a squarefree integer, over a base field B (ℚ or ℚ(i)); elements a + b√D.
# QS{D} = ℚ(√D) (negative D gives a complex field); ℚ(i)(√D) (Step 7) uses D > 0.
struct QSB{D,B}
    a::B
    b::B
end
const QS{D} = QSB{D,Q}
Base.zero(::Type{QSB{D,B}}) where {D,B} = QSB{D,B}(zero(B), zero(B))
Base.one(::Type{QSB{D,B}}) where {D,B} = QSB{D,B}(one(B), zero(B))
Base.iszero(x::QSB) = iszero(x.a) && iszero(x.b)
Base.isone(x::QSB) = isone(x.a) && iszero(x.b)
Base.:(==)(x::QSB{D,B}, y::QSB{D,B}) where {D,B} = x.a == y.a && x.b == y.b
Base.:+(x::QSB{D,B}, y::QSB{D,B}) where {D,B} = QSB{D,B}(x.a + y.a, x.b + y.b)
Base.:-(x::QSB{D,B}, y::QSB{D,B}) where {D,B} = QSB{D,B}(x.a - y.a, x.b - y.b)
Base.:-(x::QSB{D,B}) where {D,B} = QSB{D,B}(-x.a, -x.b)
Base.:*(x::QSB{D,B}, y::QSB{D,B}) where {D,B} =
    QSB{D,B}(x.a * y.a + D * (x.b * y.b), x.a * y.b + x.b * y.a)
Base.:*(n::Integer, x::QSB{D,B}) where {D,B} = QSB{D,B}(n * x.a, n * x.b)
function Base.inv(x::QSB{D,B}) where {D,B}
    n = x.a * x.a - D * (x.b * x.b)
    QSB{D,B}(x.a / n, -x.b / n)
end
Base.:/(x::QSB{D,B}, y::QSB{D,B}) where {D,B} = x * inv(y)
toQS(::Type{QS{D}}, p::UPoly{Q}) where {D} = UPoly{QS{D}}(QS{D}[QS{D}(c, Q(0)) for c in p.c])

# n = s^2 d with d squarefree (sign kept in d)
function sqfree_split(n::BigInt)
    s, d = big(1), big(1)
    for (p, k) in factorint(abs(n))
        s *= p^(k ÷ 2)
        d *= p^(k % 2)
    end
    s, (n < 0 ? -d : d)
end

# Rioboo's LogToAtan (Bronstein §2.8). For A, B ∈ K[x] (K real), B ≠ 0: polynomials p₁, …, pₖ with
#   Σ 2 atan(pⱼ)  ≡  2 atan(A/B)  ≡  i log((A + iB)/(A - iB))      (equal derivatives)
# Unlike atan(A/B), which jumps by ±π at the real zeros of B, a sum of atans of polynomials is
# continuous on the real line. Recursion: B | A gives A/B; deg A < deg B swaps to (-B, A);
# otherwise B D - A C = G = gcd(A, B) and 2 atan((A D + B C)/G) + LogToAtan(D, C).
function log_to_atan(A::UPoly{T}, B::UPoly{T}) where {T}
    out = UPoly{T}[]
    while true
        q, r = divrem(A, B)
        if iszero(r)
            push!(out, q)
            return out
        end
        if degree(A) < degree(B)
            A, B = -B, A
            continue
        end
        D, C, G = gcdex(B, -A)
        p, r = divrem(A * D + B * C, G)
        iszero(r) || throw(RischError("log_to_atan: G does not divide A D + B C"))
        push!(out, p)
        A, B = D, C
    end
end

# LogToAtan(U, √e V) for a real non-square e > 0 (the d < 0 case of a quadratic pair), without
# adjoining √e: under √e ↦ -√e, A = U is even and B = √e V odd, and this persists through the
# recursion, so every pⱼ = √e uⱼ and only the rational parts are needed. Two states:
#   even: A = a, B = √e b  (gcdex: e b d - a c = G; D = √e d, C = c; next: odd with (d, c))
#   odd:  A = √e a, B = b  (gcdex: b D - e a c = G; C = √e c;        next: even with (D, c))
# Returns [uⱼ] with Σ 2 atan(√e uⱼ) ≡ 2 atan(U/(√e V)). `ek` is e in the coefficient field, so
# this also works at a tower level (U, V ∈ K[θ]).
function log_to_atan_sqrt(a::UPoly{T}, b::UPoly{T}, ek::T) where {T}
    out = UPoly{T}[]
    even = true
    while true
        q, r = divrem(a, b)
        if iszero(r)                                    # A/B = √e·q/e (even) or √e·q (odd)
            push!(out, even ? scale(inv(ek), q) : q)
            return out
        end
        if degree(a) < degree(b)                        # (A, B) -> (-B, A)
            a, b = -b, a
            even = !even
            continue
        end
        if even
            d, c, G = gcdex(scale(ek, b), -a)
        else
            d, c, G = gcdex(b, -scale(ek, a))
        end
        u, r = divrem(a * d + b * c, G)                 # (A D + B C)/G = √e u in both states
        iszero(r) || throw(RischError("log_to_atan_sqrt: G does not divide the numerator"))
        push!(out, u)
        a, b = d, c
        even = !even
    end
end

# Residues are the two roots a = α ± β√d of the irreducible quadratic `rest`. With
# W = gcd(D, A - a D') = U + √d V:   a log W + ā log W̄ is
#   α log(U² - d V²) + β√d log((U + √d V)/(U - √d V))                 (d > 1)
#   α log(U² + e V²) + β√e LogToAtan(U, √e V),   e = -d               (d < 0)
function quad_terms(A::CX, D::CX, dD::CX, rest::CX)
    rest = monic(rest)
    p0, p1 = rest.c[1], rest.c[2]
    α = -p1 / 2
    Δ = p1^2 - 4 * p0
    iszero(Δ) && return nothing
    s, d = sqfree_split(numerator(Δ) * denominator(Δ))
    (d == 1 || abs(d) > 10^9) && return nothing
    β = Q(s) / (2 * denominator(Δ))
    dd = Int(d)
    S = QS{dd}
    a = S(α, β)
    W = gcd(toQS(S, D), toQS(S, A) - scale(a, toQS(S, dD)))
    degree(W) > 0 || return nothing
    U = CX(Q[w.a for w in W.c])
    V = CX(Q[w.b for w in W.c])
    logs = Tuple{Q,CX}[]
    quads = Any[]
    iszero(α) || push!(logs, (α, U * U - dd * (V * V)))
    if !iszero(V)
        if dd > 0
            push!(quads, QuadLog(β, dd, U, V))
        elseif !iszero(U)
            # W = U + i√e V: β√e LogToAtan(U, √e V) = Σ 2β√e atan(√e uⱼ)
            e = -dd
            for u in log_to_atan_sqrt(U, V, Q(e))
                push!(quads, QuadAtan(2 * β, e, frac(u), false))
            end
        end
    end
    logs, quads
end

# log and atan terms for one irreducible quadratic residue factor q over ℚ; false if not handled.
# Residues α ± βi (β rational): with W = gcd(D, A - (α + βi) D') = U + iV,
#   α log(U² + V²) + β LogToAtan(U, V)  (atans of polynomials);  otherwise `quad_terms` (Stage 5a).
function quad_factor!(logs, atans, quads, A::CX, D::CX, dD::CX, q::CX)
    q = monic(q)
    p0, p1 = q.c[1], q.c[2]
    α = -p1 / 2
    s = rat_sqrt(-(p1^2 - 4 * p0))          # sqrt(-discriminant), only if rational
    if s !== nothing && !iszero(s)
        β = s / 2
        a = QI(α, β)
        W = gcd(toQI(D), toQI(A) - scale(a, toQI(dD)))
        U = CX(C[w.re for w in W.c])
        V = CX(C[w.im for w in W.c])
        iszero(α) || push!(logs, (α, U * U + V * V))
        if !iszero(U) && !iszero(V)
            for p in log_to_atan(U, V)              # β LogToAtan(U, V) ≡ 2β atan(U/V)
                push!(atans, (2 * β, frac(p)))
            end
        end
        return true
    end
    qt = quad_terms(A, D, dD, q)            # irrational or non-square complex residues (5a)
    qt === nothing && return false
    append!(logs, qt[1])
    append!(quads, qt[2])
    true
end

# Step R2 (real form of a RootSum). An irreducible quartic residue factor q over ℚ whose roots
# are u ± iv, u′ ± iv′ with u, v, u′, v′ in one real quadratic field ℚ(√d) (then ℚ(α) = ℚ(i, √d)
# and q = q₁·q₂ over ℚ(√d), qₖ = z² - 2uₖ z + uₖ² + vₖ²). The sum s of a conjugate pair is a root of
#   S(t) = Π_{i<j} (t - αᵢ - αⱼ),   S² = res_z(q(z), q(t - z)) / (16 q(t/2)),
# so d is read off a linear or quadratic factor of S over ℚ. Returns candidates (d, q₁), q₁ monic
# quadratic over ℚ(√d) dividing q (not yet checked for complex roots).
function conj_pair_factors(q::CX)
    c = q.c
    K = CXF
    lin = UPoly{K}(K[frac(xpoly(Q)), kconst(Q(-1))])            # t - z, as a polynomial in z
    qtz = foldr((ci, acc) -> acc * lin + UPoly{K}(K[kconst(ci)]), c; init = zero(UPoly{K}))
    r = resultant(UPoly{K}(K[kconst(ci) for ci in c]), qtz)
    out = Any[]
    isone(r.den) || return out
    S2, r0 = divrem(r.num, CX(Q[16 * c[k] / Q(2)^(k - 1) for k in eachindex(c)]))
    iszero(r0) || return out
    for g in factor_Q(quo(S2, gcd(S2, deriv(S2))))
        degree(g) <= 2 || continue
        # the quadratic whose roots are in ℚ(√d): for a linear g (s rational) both pairs have sum
        # s, so q = (z² - sz + p₁)(z² - sz + p₂) and p₁, p₂ are the roots of y² - P y + Pr
        if degree(g) == 1
            s = -g.c[1]
            c[4] == -2s || continue
            P, Pr = c[3] - s^2, c[1]
            e0, e1 = Pr, -P                                     # y² + e1 y + e0
        else
            e0, e1 = g.c[1], g.c[2]
        end
        Δ = e1^2 - 4 * e0
        Δ > 0 || continue
        sd, d = sqfree_split(numerator(Δ) * denominator(Δ))
        (d == 1 || d > 10^9) && continue
        S = QS{Int(d)}
        root = S(-e1 / 2, Q(sd) / (2 * denominator(Δ)))         # (-e1 + √Δ)/2
        qS = toQS(S, q)
        if degree(g) == 1
            q1 = UPoly{S}(S[root, cfromQ(S, -s), one(S)])
        else                                                    # q₁ = gcd(q(z), q(s - z))
            l = UPoly{S}(S[root, -one(S)])
            q1 = gcd(qS, foldr((ci, acc) -> acc * l + UPoly{S}(S[ci]), qS.c; init = zero(UPoly{S})))
        end
        degree(q1) == 2 && iszero(rem(qS, q1)) && push!(out, (Int(d), q1))
    end
    out
end

# log and atan terms over ℚ(√d) for an irreducible quartic residue factor q (see above); false if
# its roots are not of that kind (q then stays a RootSum). Each conjugate pair u ± iv gives, as in
# `quad_factor!`, with W = gcd(D, A - (u + iv) D') = U + iV, U, V ∈ ℚ(√d)[x]:
#   u log(U² + V²) + v LogToAtan(U, V)  (atans of polynomials).
# The terms of both pairs (σ-conjugate, σ: √d ↦ -√d) are returned together as one
# RationalIntegral over ℚ(√d) in `quads`: only their sum has a derivative in ℚ(x).
function quartic_real!(quads, A::CX, D::CX, dD::CX, q::CX)
    for (d, q1) in conj_pair_factors(monic(q))
        S = QS{d}
        B2 = QSB{d,QI}
        qS = toQS(S, monic(q))
        pairs = Tuple{S,S}[]
        for qk in (q1, quo(qS, q1))
            u = -qk.c[2] / cfromQ(S, Q(2))
            v = qs_sqrt(qk.c[1] - u * u)                        # a square in ℚ(√d), d > 0: v² > 0
            (v === nothing || iszero(v)) && break
            push!(pairs, (u, v))
        end
        length(pairs) == 2 || continue
        toB2(p::CX) = UPoly{B2}(B2[B2(QI(a, Q(0)), zero(QI)) for a in p.c])
        logs = Tuple{S,UPoly{S}}[]
        atans = Tuple{S,Frac{UPoly{S}}}[]
        for (u, v) in pairs
            α = B2(QI(u.a, v.a), QI(u.b, v.b))
            W = gcd(toB2(D), toB2(A) - scale(α, toB2(dD)))
            U = UPoly{S}(S[S(w.a.re, w.b.re) for w in W.c])
            V = UPoly{S}(S[S(w.a.im, w.b.im) for w in W.c])
            iszero(u) || push!(logs, (u, U * U + V * V))
            if !iszero(U) && !iszero(V)
                for p in log_to_atan(U, V)
                    push!(atans, (2 * v, frac(p)))
                end
            end
        end
        push!(quads, RationalIntegral(zero(Frac{UPoly{S}}), logs, atans, Any[]))
        return true
    end
    false
end

# an element of ℚ(√d)(x) that lies in ℚ(x) (normal form: then every coefficient is rational)
function qs_down(f::Frac{UPoly{QSB{d,Q}}}) where {d}
    down(p) = all(c -> iszero(c.b), p.c) ? CX(Q[c.a for c in p.c]) :
              throw(RischError("real form of a RootSum: derivative not in ℚ(x)"))
    frac(down(f.num), down(f.den))
end

# Step SD. Over C = B(t) (t the outermost constant generator: e, log 2, …), the factor of D that does
# not involve t: clear the denominators of D's coefficients and write D = Σ_k t^k E_k(s), E_k ∈ B[s];
# G = gcd_k E_k. Returns G (as a polynomial over C) when 0 < deg G < deg D, else nothing.
function tfree_factor(D::UPoly{Frac{UPoly{B}}}) where {B}
    C = Frac{UPoly{B}}
    PB = UPoly{B}
    L = reduce((a, b) -> quo(a * b, gcd(a, b)), (c.den for c in D.c if !iszero(c)); init = one(PB))
    Dh = PB[iszero(c) ? zero(PB) : c.num * quo(L, c.den) for c in D.c]   # coefficients in B[t]
    kmax = maximum(degree(p) for p in Dh)
    G = zero(PB)
    for k in 0:kmax
        Ek = PB(B[k < length(p.c) ? p.c[k + 1] : zero(B) for p in Dh])
        iszero(Ek) || (G = iszero(G) ? monic(Ek) : gcd(G, Ek))
    end
    (0 < degree(G) < degree(D)) || return nothing
    UPoly{C}(C[kconst(c) for c in G.c])
end
tfree_factor(D::UPoly) = nothing

function log_part(A::UPoly{C}, D::UPoly{C}) where {C}
    if rational_tfield(C) && !iszero(A)
        G = tfree_factor(D)
        if G !== nothing                       # A/D = A₁/G + A₂/H: separate residue polynomials (SD)
            H, r = divrem(D, G)
            iszero(r) || throw(RischError("tfree_factor: G does not divide D"))
            sH, uG, g = gcdex(H, G)            # sH·H + uG·G = 1 (D squarefree: G, H coprime)
            isone(g) || throw(RischError("tfree_factor: G and D/G are not coprime"))
            p1 = log_part(rem(A * sH, G), G)
            p2 = log_part(rem(A * uG, H), monic(H))
            return vcat(p1[1], p2[1]), vcat(p1[2], p2[2]), vcat(p1[3], p2[3]), vcat(p1[4], p2[4])
        end
    end
    CXl = UPoly{C}
    CXFl = Frac{UPoly{C}}
    logs = Tuple{C,CXl}[]
    atans = Tuple{C,CXFl}[]
    unresolved = Any[]
    quads = Any[]
    iszero(A) && return logs, atans, unresolved, quads
    dD = deriv(D)
    Rz = residue_resultant(D, A, dD)                 # R(z) = res_x(D, A - z D')
    iszero(Rz) && throw(RischError("zero resultant in the residue computation"))
    degree(Rz) <= 0 && return logs, atans, unresolved, quads
    Rsf = quo(Rz, gcd(Rz, deriv(Rz)))        # distinct residues
    roots = constant_roots(Rsf)
    rest = Rsf
    for a in roots
        W = gcd(D, A - scale(a, dD))
        degree(W) > 0 && push!(logs, (a, W))
        rest = quo(rest, CXl(C[-a, one(C)]))
    end
    degree(rest) == 0 && return logs, atans, unresolved, quads
    hard = rest                              # residue factors left for RootSum
    if C === Q                               # quadratic factors over ℚ: logs and atans (steps 5/5b)
        hard = one(CXl)
        for q in (degree(rest) > 2 ? factor_Q(rest) : [rest])
            degree(q) == 2 && quad_factor!(logs, atans, quads, A, D, dD, q) && continue
            degree(q) == 4 && quartic_real!(quads, A, D, dD, q) && continue
            hard = hard * q
        end
    end
    degree(hard) > 0 && push!(unresolved, (hard, A, D))
    logs, atans, unresolved, quads
end

function integrate_rational(f::Frac{UPoly{C}}) where {C}
    iszero(f) && return RationalIntegral(zero(typeof(f)), Tuple{C,UPoly{C}}[],
                                         Tuple{C,Frac{UPoly{C}}}[], Any[])
    g, Qp, R, Dsf = hermite_reduce(dx, f.num, f.den)
    rational = g + frac(integrate_poly(Qp))
    logs, atans, unresolved, quads = log_part(R, Dsf)
    RationalIntegral(rational, logs, atans, unresolved, quads)
end

# d/dx of the computed antiderivative, in ℚ(x) (for self-verification)
function derivative_of(res::RationalIntegral{C}) where {C}
    F = typeof(res.rational)
    tot = dx(res.rational)
    for (c, w) in res.logs
        tot = tot + kconst(c) * frac(deriv(w), w)
    end
    for (c, u) in res.atans
        tot = tot + kconst(c) * dx(u) / (one(F) + u * u)
    end
    for q in res.quads
        if q isa RationalIntegral                    # real form of a quartic RootSum, over ℚ(√d)
            tot = tot + qs_down(derivative_of(q))
        elseif q isa QuadLog  # d/dx [β√d log(W/W̄)] = 2βd (V'U - U'V)/(U² - dV²)
            U, V = q.U, q.V
            tot = tot + kconst(2 * q.β * q.d) * frac(deriv(V) * U - deriv(U) * V, U * U - q.d * (V * V))
        else                  # c√e atan(√e u):  c e u'/(1 + e u²);  c√e atan(u/√e):  c e u'/(e + u²)
            u, e = q.u, Q(q.e)
            den = q.inverted ? kconst(e) + u * u : one(F) + kconst(e) * u * u
            tot = tot + kconst(q.c * e) * dx(u) / den
        end
    end
    tot
end
check_result(res::RationalIntegral, f::Frac) = isempty(res.unresolved) && derivative_of(res) == f

# ---------------------------------------------------------------------------
# TermInterface front end: term -> ℚ(x)
# ---------------------------------------------------------------------------
safe_iscall(t) = try iscall(t) === true catch; false end

# Numeric leaves of symbolic packages. Besides Julia numbers these include
#  * callable constants (SimpleExpressions represents the `-1` in `x^2 - 1` as a
#    function-like object): evaluated with `t()`, which fails for variables;
#  * `Basic` numbers (SymEngine) and anything else numeric: read from the exact
#    printed form.
function leaf_rational(t)
    t isa Integer && return Q(t)
    t isa Rational && return Q(t)
    t isa AbstractFloat && return isfinite(t) ? rationalize(BigInt, t) : nothing
    if t isa Function
        v = try
            t()
        catch
            nothing
        end
        v isa Real && return leaf_rational(v)
    end
    s = string(t)
    m = match(r"^(-?\d+)(?:/(\d+))?$", s)
    if m !== nothing
        n = parse(BigInt, m.captures[1])
        d = m.captures[2] === nothing ? big(1) : parse(BigInt, m.captures[2])
        return Q(n // d)
    end
    occursin(r"^-?(\d+\.\d*|\.\d+|\d+)([eE][+-]?\d+)?$", s) ?
        rationalize(BigInt, parse(Float64, s)) : nothing
end

opname(op) = op isa Symbol ? op : (op isa Function ? nameof(op) : Symbol(string(op)))

# the integer value of a constant rational function, or nothing
function const_int(f::CXF)
    (isone(f.den) && degree(f.num) <= 0) || return nothing
    c = isempty(f.num.c) ? Q(0) : f.num.c[1]
    isone(denominator(c)) ? Int(numerator(c)) : nothing
end

const NONRATIONAL = (:exp, :log, :sin, :cos, :tan, :atan, :sinh, :cosh, :tanh, :abs, :sqrt, :cbrt)

function parse_rational(t, xk::String)::CXF
    if safe_iscall(t)
        args = arguments(t)
        if !isempty(args)
            n = opname(operation(t))
            n in NONRATIONAL && throw(RischNotImplemented(
                "`$n` is not a rational function; integrands with exp/log towers " *
                "are planned for Stage 2/3 (see the roadmap in Risch.jl)"))
            a = CXF[parse_rational(u, xk) for u in args]
            if n === :+
                return foldl(+, a; init = zero(CXF))
            elseif n === :-
                return length(a) == 1 ? -a[1] : a[1] - foldl(+, a[2:end]; init = zero(CXF))
            elseif n === :*
                return foldl(*, a; init = one(CXF))
            elseif n === :/ && length(a) == 2
                return a[1] / a[2]
            elseif n === :inv && length(a) == 1
                return inv(a[1])
            elseif n === :^ && length(a) == 2
                k = const_int(a[2])
                (k === nothing || abs(k) > 10_000) &&
                    throw(RischNotImplemented("only small integer powers are rational functions"))
                return a[1]^k
            else
                throw(RischNotImplemented("unsupported operation `$n`"))
            end
        end
    end
    string(t) == xk && return frac(xpoly(Q))
    r = leaf_rational(t)
    r !== nothing && return kconst(r)
    throw(RischNotImplemented("symbol `$t` is not the integration variable; " *
                              "symbolic parameters are not supported yet"))
end

# ---------------------------------------------------------------------------
# Output: build a term from the exact result, by *calling operations as functions*
# ---------------------------------------------------------------------------
fitint(n::BigInt) = typemin(Int) <= n <= typemax(Int) ? Int(n) : n
function num(c::Q)
    n, d = numerator(c), denominator(c)
    isone(d) && return fitint(n)
    (typemin(Int) <= n <= typemax(Int) && d <= typemax(Int)) ? Int(n) // Int(d) : c
end

# A generator tⱼ of a transcendental constant field ℚ(t₁, …, tₖ) (Step 6): tⱼ = exp(arg) or
# log(arg), arg ∈ ℚ. The field type only knows "k indeterminates"; what they stand for is
# this list, kept by the tower (`T.consts`) and by the Builder (for output).
struct ConstGen
    kind::Symbol          # :exp or :log
    arg::Q
end
Base.:(==)(a::ConstGen, b::ConstGen) = a.kind === b.kind && a.arg == b.arg
Base.hash(g::ConstGen, h::UInt) = hash(g.arg, hash(g.kind, h))

struct Builder
    build::Any
    lift::Any
    x::Any
    consts::Vector{ConstGen}  # meaning of the indeterminates of the constant field (output)
end
Builder(build, lift, x) = Builder(build, lift, x, ConstGen[])
const OPS = Dict{Symbol,Function}(:+ => +, :* => *, :/ => /, :^ => ^, :exp => exp,
                                  :log => log, :atan => atan, :sqrt => sqrt,
                                  :sin => sin, :cos => cos, :tan => tan,
                                  # SpecialFunctions (Step 8a): Ei, Si, Ci, erf, erfi
                                  :Ei => expinti, :Si => sinint, :Ci => cosint, :erf => erf, :erfi => erfi)
mk(b::Builder, name::Symbol, args...) = b.build(OPS[name], args...)

# a constant of the differential field as a term (part of the constant-field interface;
# only C = ℚ is implemented: rationals are lifted into the package's number type)
cterm(b::Builder, c::Q) = b.lift(num(c))
function cterm(b::Builder, c::QS{d}) where {d}         # a + b√d, with sqrt(d) kept symbolic
    iszero(c.b) && return cterm(b, c.a)
    r = mk(b, :sqrt, b.lift(d))
    s = isone(c.b) ? r : mk(b, :*, cterm(b, c.b), r)
    iszero(c.a) ? s : mk(b, :+, cterm(b, c.a), s)
end
cterm(b::Builder, c) = throw(RischNotImplemented(
    "output of constants of type $(typeof(c)) is not implemented"))

# constants of ℚ(i) and ℚ(i)(√d) in real-form output: they must be real (Step 7)
function cterm(b::Builder, c::QI)
    iszero(c.im) || throw(RischError("a non-real constant $c reached the real-form output"))
    cterm(b, c.re)
end
function cterm(b::Builder, c::QSB{d,QI}) where {d}
    (iszero(c.a.im) && iszero(c.b.im)) || throw(RischError("a non-real constant $c reached the real-form output"))
    cterm(b, QS{d}(c.a.re, c.b.re))
end

# c ∈ ℚ(t₁, …, tₖ) = B(tₖ): a rational function of tₖ with coefficients in B, tₖ from b.consts
function cterm(b::Builder, c::Frac{<:UPoly})
    k = cdepth(typeof(c))
    k <= length(b.consts) || throw(RischError(
        "constant field with $k generators but only $(length(b.consts)) are described"))
    b.consts[k].kind === :expi && return cterm_expi(b, c, b.consts[k].arg)
    t = constgen_term(b, b.consts[k])
    n = cpoly_term(b, c.num, t)
    isone(c.den) ? n : mk(b, :/, n, cpoly_term(b, c.den, t))
end
# a real (σ-invariant) constant c ∈ B(τ), τ = e^(i·a): c = (N·σD)/(D·σD) with σ-invariant Laurent
# polynomials in τ, written with cos(k·a) and sin(k·a) (as for a :trig level of a tower)
function cterm_expi(b::Builder, c::Frac{<:UPoly}, a::Q)
    B = eltype(c.num.c)
    sD = Dict{Int,B}(-(j - 1) => cconj_g(b.consts, d) for (j, d) in enumerate(c.den.c) if !iszero(d))
    A = laurent_mul(laurent_of(c.num), sD)
    Bd = laurent_mul(laurent_of(c.den), sD)
    n = cterm_laurent(b, A, a, B)
    if length(Bd) == 1 && haskey(Bd, 0)
        return isone(Bd[0]) ? n : mk(b, :/, n, cterm(b, Bd[0]))
    end
    mk(b, :/, n, cterm_laurent(b, Bd, a, B))
end
function cterm_laurent(b::Builder, L::Dict, a::Q, ::Type{B}) where {B}
    all(k -> haskey(L, -k), keys(L)) || throw(RischError("a constant in the real-form output is not real"))
    I = cimag(B)
    ts = Any[]
    c0 = get(L, 0, zero(B))
    iszero(c0) || push!(ts, cterm(b, c0))
    for k in sort([k for k in keys(L) if k > 0])
        ck, cm = L[k], L[-k]
        ka = cterm(b, k * a)
        for (coef, fn) in ((ck + cm, :cos), (I * (ck - cm), :sin))
            iszero(coef) && continue
            tr = mk(b, fn, ka)
            push!(ts, isone(coef) ? tr : mk(b, :*, cterm(b, coef), tr))
        end
    end
    isempty(ts) && return b.lift(0)
    length(ts) == 1 ? ts[1] : mk(b, :+, ts...)
end

constgen_term(b::Builder, g::ConstGen) =
    g.kind === :exp ? mk(b, :exp, cterm(b, g.arg)) :
    g.kind === :log ? mk(b, :log, cterm(b, g.arg)) :
    throw(RischError("unknown constant generator kind $(g.kind)"))
function cpoly_term(b::Builder, p::UPoly, t)
    iszero(p) && return b.lift(0)
    ts = Any[]
    for (i, c) in enumerate(p.c)
        iszero(c) && continue
        k = i - 1
        if k == 0
            push!(ts, cterm(b, c))
        else
            tk = k == 1 ? t : mk(b, :^, t, b.lift(k))
            push!(ts, isone(c) ? tk : mk(b, :*, cterm(b, c), tk))
        end
    end
    length(ts) == 1 ? ts[1] : mk(b, :+, ts...)
end

default_build(op, args...) = op(args...)

# Constants such as sqrt(3) must stay symbolic. SimpleExpressions-like types defer
# evaluation only when a symbolic variable is involved, so a constant-only call
# `op(args...)` is built by substituting into `op(x, args[2:end]...)` (the
# documented `u(value, :)` substitution); other types simply apply the operation.
function placeholder_call(x, op, args)
    isempty(args) && return nothing
    try
        u = op(x, args[2:end]...)
        u isa Function || return nothing
        r = u(args[1], :)
        r isa Function ? r : nothing
    catch
        nothing
    end
end
function deferred_call(x, op, args)
    r = placeholder_call(x, op, args)
    r === nothing ? op(args...) : r
end
function auto_build(f, x)
    typeof(x) <: Function || return default_build
    (op, args...) -> any(a -> a isa Function, args) ? op(args...) : deferred_call(x, op, args)
end

function auto_lift(f, x)
    for t in (f, x)
        if t isa Number && !(t isa Real)
            T = typeof(t)
            return v -> try
                T(v)
            catch
                v
            end
        end
    end
    identity
end

function poly_term(b::Builder, p::UPoly)
    iszero(p) && return b.lift(0)
    ts = Any[]
    for (i, c) in enumerate(p.c)
        iszero(c) && continue
        k = i - 1
        if k == 0
            push!(ts, cterm(b, c))
        else
            xk = k == 1 ? b.x : mk(b, :^, b.x, b.lift(k))
            push!(ts, isone(c) ? xk : mk(b, :*, cterm(b, c), xk))
        end
    end
    length(ts) == 1 ? ts[1] : mk(b, :+, ts...)
end
frac_term(b::Builder, f::Frac{<:UPoly}) =
    isone(f.den) ? poly_term(b, f.num) : mk(b, :/, poly_term(b, f.num), poly_term(b, f.den))

function to_term(b::Builder, res::RationalIntegral)
    ts = Any[]
    iszero(res.rational) || push!(ts, frac_term(b, res.rational))
    for (c, w) in res.logs
        l = mk(b, :log, poly_term(b, w))
        push!(ts, isone(c) ? l : mk(b, :*, cterm(b, c), l))
    end
    for (c, u) in res.atans
        l = mk(b, :atan, frac_term(b, u))
        push!(ts, isone(c) ? l : mk(b, :*, cterm(b, c), l))
    end
    for q in res.quads
        if q isa RationalIntegral
            push!(ts, to_term(b, q))
        elseif q isa QuadLog
            r = mk(b, :sqrt, b.lift(q.d))
            top = mk(b, :+, poly_term(b, q.U), mk(b, :*, r, poly_term(b, q.V)))
            bot = mk(b, :+, poly_term(b, q.U), mk(b, :*, b.lift(-1), r, poly_term(b, q.V)))
            l = mk(b, :log, mk(b, :/, top, bot))
            push!(ts, isone(q.β) ? mk(b, :*, r, l) : mk(b, :*, b.lift(num(q.β)), r, l))
        else
            r = mk(b, :sqrt, b.lift(q.e))
            arg = q.inverted ? mk(b, :/, frac_term(b, q.u), r) : mk(b, :*, r, frac_term(b, q.u))
            l = mk(b, :atan, arg)
            push!(ts, isone(q.c) ? mk(b, :*, r, l) : mk(b, :*, b.lift(num(q.c)), r, l))
        end
    end
    isempty(ts) && return b.lift(0)
    length(ts) == 1 ? ts[1] : mk(b, :+, ts...)
end

# ---------------------------------------------------------------------------
# Stage 2: towers of transcendental monomials  ℚ(x)(θ₁)…(θₙ)
#
# Level i holds θᵢ = exp(u) or log(u) with u ∈ Kᵢ₋₁ and Dθᵢ ∈ Kᵢ₋₁[θᵢ]:
#   exp(u):  Dθ = u' θ          log(u):  Dθ = u'/u
# The field Kᵢ = Frac{UPoly{Kᵢ₋₁}} is a *type*, so elements know their level.
# A monomial is only added when it is algebraically independent of the earlier
# ones; otherwise it is expressed through them (exp(2x) = θ², exp(log x) = x,
# log(x²-1) = log(x-1) + log(x+1), ...). Dependence is detected by exact linear
# algebra over ℚ (Risch structure theorem for logarithmic / exponential towers).
# ---------------------------------------------------------------------------
struct Level
    kind::Symbol          # :exp or :log
    arg::Any              # u ∈ Kᵢ₋₁
    dtheta::Any           # Dθᵢ ∈ Kᵢ₋₁[θᵢ]
    seq::Int              # creation number among exp levels (0 for log)
end

mutable struct Tower{C}          # C: type of the constants of the differential field
    xk::String
    levels::Vector{Level}
    Ts::Vector{DataType}      # Ts[i+1] is the type of Kᵢ
    scales::Dict{Int,Int}     # exp-generator refinement hints (see Restart)
    nexp::Int
    consts::Vector{ConstGen}  # meaning of the generators of C when C = ℚ(t₁, …, tₖ) (Step 6)
    subst::Any                # parse hook (term, T) -> element or nothing (Step 10: radicals)
end
Tower(::Type{C}, xk::String, scales::Dict{Int,Int}, consts::Vector{ConstGen} = ConstGen[]) where {C} =
    Tower{C}(xk, Level[], DataType[Frac{UPoly{C}}], scales, 0, consts, nothing)
ctype(::Tower{C}) where {C} = C

# --- interface every constant field C must provide ----------------------------
#   cfromQ(C, q)     embedding ℚ -> C
#   crational(c)     the value of c as a rational number when c ∈ ℚ, else nothing
#   cflat_all(C, cs) coordinates over ℚ of a list of constants (aligned; see `flat`)
#   constant_roots   roots in C of a polynomial over C
#   cterm(b, c)      the constant as a term of the user's package (output)
# Only C = ℚ is implemented. The fallbacks raise RischNotImplemented rather than guess:
# e.g. answering "not rational" for a constant that is rational in disguise would make
# the integer test for the cancellation exponent (rde) silently wrong.
cfromQ(::Type{Q}, q::Q) = q
cfromQ(::Type{T}, q::Q) where {T} = throw(RischNotImplemented(
    "embedding of ℚ into the constant field $T is not implemented"))

crational(c::Q) = c
crational(c) = throw(RischNotImplemented(
    "deciding whether a constant of type $(typeof(c)) is rational is not implemented"))

# the rational integer value of a constant, or nothing
function cinteger(c)
    q = crational(c)
    (q !== nothing && isone(denominator(q))) ? q : nothing
end

# lift a constant c ∈ C (not just a rational number) to level j
lconst(T::Tower, c, j::Int) = liftto(T, kconst(c), j)

struct Restart <: Exception
    seq::Int
    q::Int
end

levelof(T::Tower, f) = begin
    i = findfirst(==(typeof(f)), T.Ts)
    i === nothing && throw(RischError("element does not belong to the tower"))
    i - 1
end
lift1(f) = (K = typeof(f); frac(UPoly{K}(K[f])))
function liftto(T::Tower, f, j::Int)
    while levelof(T, f) < j
        f = lift1(f)
    end
    f
end
theta(T::Tower, i::Int) = frac(xpoly(T.Ts[i]))          # θᵢ ∈ Kᵢ
lq(T::Tower{C}, c::Q, j::Int) where {C} = liftto(T, kconst(cfromQ(C, c)), j)

# constant value (∈ C) of a tower element, or nothing. The tower says where the constants end
# (C may itself be a fraction field), so this walks down the levels instead of dispatching on types.
function const_value(T::Tower{C}, f) where {C}
    i = levelof(T, f)
    while true
        (isone(f.den) && degree(f.num) <= 0) || return nothing
        isempty(f.num.c) && return zero(C)
        c = f.num.c[1]
        i == 0 && return c
        f, i = c, i - 1
    end
end

# --- the derivation on every level -------------------------------------------
function D(T::Tower, i::Int, f::Frac{<:UPoly})
    i == 0 && return dx(f)
    frac(Dp(T, i, f.num) * f.den - f.num * Dp(T, i, f.den), f.den * f.den)
end
function Dp(T::Tower, i::Int, p::UPoly)
    K = T.Ts[i]                                       # type of Kᵢ₋₁
    res = UPoly{K}(K[D(T, i - 1, c) for c in p.c])
    res + deriv(p) * T.levels[i].dtheta
end
D(T::Tower, f) = D(T, levelof(T, f), f)

# --- differential constants ----------------------------------------------------
# `const_value` is structural: it recognises elements written as a constant of C. The
# algorithm needs the semantic notion, D f = 0 (residue criterion, constant ratios in the
# log structure theorem, the cancellation exponent of the Risch DE). In a valid tower of
# monomials over C the two agree: no monomial introduces new constants, so every element
# with D f = 0 lies in C. `dconst_value` therefore tries the cheap structural test first and
# only then differentiates; a differential constant that is not structurally in C means the
# tower is not a valid monomial extension, which is reported as an internal error rather
# than silently treated as "not constant".
is_constant(T::Tower, f) = const_value(T, f) !== nothing || iszero(D(T, f))

function dconst_value(T::Tower, f)
    v = const_value(T, f)
    v === nothing || return v
    iszero(D(T, f)) && throw(RischError(
        "an element with derivative 0 is not in the constant field: the tower is not a valid " *
        "monomial extension (new constants appeared)"))
    nothing
end

# --- ℚ-linear dependence between field elements -------------------------------
plcm(a::P, b::P) where {P<:UPoly} = quo(a * b, gcd(a, b))

# coordinates of constants over ℚ (aligned across the list): ℚ itself is one coordinate
cflat_all(::Type{Q}, cs) = [Q[c] for c in cs]
cflat_all(::Type{T}, cs) where {T} = throw(RischNotImplemented(
    "coordinates over ℚ of constants of type $T are not implemented"))

# --- B(√d) as a constant field (d squarefree, d ≠ 0, 1; B = ℚ or ℚ(i)) -------------
# Completes the arithmetic of QSB (defined with Stage 5a) and implements the constant-field
# interface. 1 and √d are linearly independent over B, so the ℚ-coordinates of a + b√d are
# those of a followed by those of b.
Base.zero(::QSB{d,B}) where {d,B} = zero(QSB{d,B})
Base.one(::QSB{d,B}) where {d,B} = one(QSB{d,B})
Base.copy(x::QSB) = x
Base.hash(x::QSB{d}, h::UInt) where {d} = hash(x.b, hash(x.a, hash(d, h)))
Base.:*(x::QSB, n::Integer) = n * x
Base.:^(x::QSB, n::Integer) = field_pow(x, n)
Base.show(io::IO, x::QSB{d}) where {d} = print(io, x.a, " + ", x.b, "√", d)

cfromQ(::Type{QSB{d,B}}, q::Q) where {d,B} = QSB{d,B}(cfromQ(B, q), zero(B))
crational(c::QSB) = iszero(c.b) ? crational(c.a) : nothing
function cflat_all(::Type{QSB{d,B}}, cs) where {d,B}
    A = cflat_all(B, B[c.a for c in cs])
    Bv = cflat_all(B, B[c.b for c in cs])
    [vcat(A[j], Bv[j]) for j in eachindex(cs)]
end

# square root in B(√d), or nothing:  (u + v√d)² = a + b√d  ⟺  u² + d v² = a, 2uv = b
function qs_sqrt(x::QSB{d,B}) where {d,B}
    S = QSB{d,B}
    a, b = x.a, x.b
    if iszero(b)
        r = csqrt(a)
        r !== nothing && return S(r, zero(B))
        s = csqrt(a / cfromQ(B, Q(d)))              # u = 0:  d v² = a
        return s === nothing ? nothing : S(zero(B), s)
    end
    disc = csqrt(a * a - d * (b * b))               # u² is a root of  t² - a t + d b²/4
    disc === nothing && return nothing
    half = inv(cfromQ(B, Q(2)))
    for u2 in ((a + disc) * half, (a - disc) * half)
        u = csqrt(u2)
        (u === nothing || iszero(u)) && continue
        y = S(u, b / (u + u))
        y * y == x && return y
    end
    nothing
end

# x^n in a field (n < 0 allowed)
function field_pow(x, n::Integer)
    n < 0 && return field_pow(inv(x), -n)
    r, b = one(x), x
    while n > 0
        isodd(n) && (r = r * b)
        n >>= 1
        n > 0 && (b = b * b)
    end
    r
end

# --- ℚ(i) as a constant field (Step 7) ------------------------------------------
Base.zero(::QI) = zero(QI)
Base.one(::QI) = one(QI)
Base.copy(a::QI) = a
Base.:*(a::QI, n::Integer) = n * a
Base.:^(a::QI, n::Integer) = field_pow(a, n)
Base.show(io::IO, a::QI) = print(io, a.re, " + ", a.im, "i")
cfromQ(::Type{QI}, q::Q) = QI(q, Q(0))
crational(c::QI) = iszero(c.im) ? c.re : nothing
cflat_all(::Type{QI}, cs) = [Q[c.re, c.im] for c in cs]

# square root in ℚ(i), or nothing:  (u + vi)² = p + qi  ⟺  u² - v² = p, 2uv = q
function qi_sqrt(a::QI)
    p, q = a.re, a.im
    if iszero(q)
        r = rat_sqrt(p)
        r !== nothing && return QI(r, Q(0))
        s = rat_sqrt(-p)
        return s === nothing ? nothing : QI(Q(0), s)
    end
    m = rat_sqrt(p^2 + q^2)                         # |a|, must be rational
    m === nothing && return nothing
    u = rat_sqrt((p + m) / 2)                       # u² = (p + |a|)/2 > 0 since q ≠ 0
    u === nothing && return nothing
    y = QI(u, q / (2 * u))
    y * y == a ? y : nothing
end

# Distinct roots in the constant field F that this finds: rational roots (common roots of the
# ℚ-coordinate polynomials: p(r)·L = Σ rᵏ vₖ for r ∈ ℚ, zero iff every coordinate is), then all
# roots once at most two remain (quadratic formula with `csqrt`). Possibly incomplete in
# degree ≥ 3, as the `constant_roots` contract allows. Used for ℚ(i), B(√d) and ℚ(t₁, …).
function constant_roots_generic(p::UPoly{F}) where {F}
    roots = F[]
    iszero(p) && return roots
    vs = cflat_all(F, p.c)
    g = zero(UPoly{Q})
    for j in eachindex(vs[1])
        g = gcd(g, UPoly{Q}(Q[v[j] for v in vs]))
    end
    rest = p
    if degree(g) > 0
        for r in rational_roots(g)
            s = cfromQ(F, r)
            push!(roots, s)
            rest = quo(rest, UPoly{F}(F[-s, one(F)]))
        end
    end
    addroot!(s) = (s in roots || push!(roots, s))
    if degree(rest) == 1
        addroot!(-rest.c[1] / rest.c[2])
    elseif degree(rest) == 2
        m = monic(rest)
        p0, p1 = m.c[1], m.c[2]
        sq = csqrt(p1 * p1 - 4 * p0)
        if sq !== nothing
            half = inv(2 * one(F))
            addroot!((-p1 + sq) * half)
            addroot!((-p1 - sq) * half)
        end
    end
    roots
end
constant_roots(p::UPoly{QSB{d,B}}) where {d,B} = constant_roots_generic(p)
constant_roots(p::UPoly{QI}) = constant_roots_generic(p)

# complex conjugation σ on constants (i -> -i). ℚ and the generators tⱼ (real constants
# e^a, log p) are fixed; in B(√d), √d is fixed for d > 0 and negated for d < 0 (B = ℚ).
cconj(c::Q) = c
cconj(c::QI) = QI(c.re, -c.im)
function cconj(c::QSB{d,B}) where {d,B}
    d > 0 && return QSB{d,B}(cconj(c.a), cconj(c.b))
    B === Q && return QSB{d,B}(c.a, -c.b)
    throw(RischError("conjugation on ℚ(i)(√d) with d < 0: use √d = i√(-d) instead"))
end
cconj(c::Frac{<:UPoly}) = frac(cpconj(c.num), cpconj(c.den))
cpconj(p::UPoly{T}) where {T} = UPoly{T}(T[cconj(c) for c in p.c])

# σ on a constant of ℚ(i)(t₁, …, tₖ) knowing what the generators are (Step 7, part 3): a real
# generator (e^a, log p) is fixed, τ = e^(i·a) (kind :expi) goes to 1/τ.
cconj_g(gens, c) = cconj(c)
function cconj_g(gens, c::Frac{<:UPoly})
    iszero(c) && return c                           # (degree of the zero numerator is -1)
    k = cdepth(typeof(c))
    n, d = cpconj_g(gens, c.num), cpconj_g(gens, c.den)
    (k <= length(gens) && gens[k].kind === :expi) || return frac(n, d)
    t = xpoly(eltype(c.num.c))                      # τ ↦ 1/τ:  p(τ) ↦ τ^(-deg p) p̃(τ)
    rv(p) = typeof(p)(reverse(p.c))
    frac(rv(n) * t^degree(c.den), rv(d) * t^degree(c.num))
end
cpconj_g(gens, p::UPoly{T}) where {T} = UPoly{T}(T[cconj_g(gens, c) for c in p.c])

# --- ℚ(t₁, …, tₖ) as a constant field (Step 6) -------------------------------------
# Purely transcendental: the type is nested rational functions,  C₀ = ℚ,  Cⱼ = Cⱼ₋₁(tⱼ) =
# Frac{UPoly{Cⱼ₋₁}}, so the existing polynomial/fraction arithmetic is the field arithmetic.
# tⱼ is treated as an indeterminate: this is exact for one generator e = exp(1) (Hermite)
# and log 2 (Lindemann); for several (e and log 2 together, say) algebraic independence is
# Schanuel's conjecture, which every CAS assumes (were it false, a constant that is really
# zero could be treated as nonzero). The meaning of each tⱼ is in `T.consts`.
cdepth(::Type{Q}) = 0
cdepth(::Type{QI}) = 0
cdepth(::Type{Frac{UPoly{B}}}) where {B} = 1 + cdepth(B)
# ℚ(t₁, …, tₖ), or ℚ(i)(t₁, …, tₖ) with base = QI (Step 7)
cfield(k::Int, base::Type = Q) = k == 0 ? base : Frac{UPoly{cfield(k - 1, base)}}
cbase(::Type{Q}) = Q
cbase(::Type{QI}) = QI
cbase(::Type{Frac{UPoly{B}}}) where {B} = cbase(B)
# ℚ(t₁, …, tₖ) with k ≥ 1 (RootSums over it: step RE)
rational_tfield(::Type{C}) where {C} = C <: Frac && cbase(C) === Q
# the generator tⱼ as an element of C = ℚ(t₁, …, tₖ), 1 ≤ j ≤ k
function tgen(::Type{Frac{UPoly{B}}}, j::Int) where {B}
    k = 1 + cdepth(B)
    1 <= j <= k || throw(ArgumentError("generator $j of a constant field with $k generators"))
    j == k ? frac(xpoly(B)) : kconst(tgen(B, j))
end

cfromQ(::Type{Frac{UPoly{B}}}, q::Q) where {B} = kconst(cfromQ(B, q))

# the normal form (coprime, monic denominator) is unique, so c ∈ ℚ iff it is a constant
# polynomial over a rational at every depth
function crational(c::Frac{<:UPoly})
    (isone(c.den) && degree(c.num) <= 0) || return nothing
    isempty(c.num.c) && return Q(0)
    crational(c.num.c[1])
end

# ℚ-coordinates, aligned across the list: multiply by the common denominator L (a ℚ-linear
# relation survives multiplication by L ≠ 0), then flatten the coefficients of the numerators.
function cflat_all(::Type{Frac{UPoly{B}}}, cs) where {B}
    isempty(cs) && return Vector{Q}[]
    P = UPoly{B}
    L = reduce(plcm, [c.den for c in cs]; init = one(P))
    nums = [c.num * quo(L, c.den) for c in cs]
    m = maximum(length(n.c) for n in nums)
    parts = [cflat_all(B, B[k <= length(n.c) ? n.c[k] : zero(B) for n in nums]) for k in 1:m]
    [reduce(vcat, (parts[k][j] for k in 1:m); init = Q[]) for j in eachindex(cs)]
end

# square roots (nothing if there is none in the field)
csqrt(q::Q) = rat_sqrt(q)
csqrt(x::QSB) = qs_sqrt(x)
csqrt(x::QI) = qi_sqrt(x)
function csqrt(c::Frac{<:UPoly})        # normal form is unique, so c = g² iff num, den are squares
    iszero(c) && return c
    a = psqrt(c.num)
    a === nothing && return nothing
    b = psqrt(c.den)
    b === nothing && return nothing
    frac(a, b)
end
# square root of a polynomial over a field B (top coefficient first), verified
function psqrt(p::UPoly{B}) where {B}
    iszero(p) && return p
    isodd(degree(p)) && return nothing
    l = csqrt(lc(p))
    l === nothing && return nothing
    n = degree(p) ÷ 2
    a = Vector{B}(undef, n + 1)               # a[k+1] = coefficient of t^k
    a[n + 1] = l
    two_l = l + l
    for k in (n - 1):-1:0                     # coefficient of t^(n+k) in a² fixes a_k
        acc = p.c[n + k + 1]
        for i in (k + 1):(n - 1)
            j = n + k - i
            (k < j < n) && (acc = acc - a[i + 1] * a[j + 1])
        end
        a[k + 1] = acc / two_l
    end
    r = UPoly{B}(a)
    r * r == p ? r : nothing
end

constant_roots(p::UPoly{F}) where {F<:Frac{<:UPoly}} = constant_roots_generic(p)

# coordinate vectors over ℚ of elements of the field K_i (level i): linear relations among the
# elements correspond exactly to linear relations among the vectors
function flat(T::Tower{C}, i::Int, elems) where {C}
    L = reduce(plcm, [e.den for e in elems]; init = one(typeof(first(elems).den)))
    nums = [e.num * quo(L, e.den) for e in elems]
    m = maximum(length(n.c) for n in nums)
    K = i == 0 ? C : T.Ts[i]                    # coefficient type of the polynomials at level i
    parts = [begin
                 col = K[k <= length(n.c) ? n.c[k] : zero(K) for n in nums]
                 i == 0 ? cflat_all(C, col) : flat(T, i - 1, col)
             end for k in 1:m]
    [reduce(vcat, (parts[k][j] for k in 1:m); init = Q[]) for j in eachindex(elems)]
end

# solve  Σ r_j cols[j] = t  over a field S (nothing if inconsistent). S = ℚ for ℚ-linear
# relations between generators; S = C for the Risch DE over C(x). Row operations are written
# as loops so that S need not be a `Number` (no array-by-scalar arithmetic is used).
function solve_columns(cols::Vector{Vector{S}}, t::Vector{S}) where {S}
    m, k = length(t), length(cols)
    M = S[j <= k ? cols[j][i] : t[i] for i in 1:m, j in 1:(k + 1)]
    ncol = k + 1
    piv = Int[]
    row = 1
    for col in 1:k
        row > m && break
        p = findfirst(i -> !iszero(M[i, col]), row:m)
        p === nothing && continue
        p += row - 1
        if p != row
            for j in 1:ncol
                M[row, j], M[p, j] = M[p, j], M[row, j]
            end
        end
        pv = inv(M[row, col])
        for j in 1:ncol
            M[row, j] = M[row, j] * pv
        end
        for i in 1:m
            (i == row || iszero(M[i, col])) && continue
            f = M[i, col]
            for j in 1:ncol
                M[i, j] = M[i, j] - f * M[row, j]
            end
        end
        push!(piv, col)
        row += 1
    end
    for i in row:m
        iszero(M[i, k + 1]) || return nothing
    end
    sol = fill(zero(S), k)
    for (i, col) in enumerate(piv)
        sol[col] = M[i, k + 1]
    end
    sol
end

function solve_relation(T::Tower, target::F, basis::Vector{F}) where {F}
    isempty(basis) && return iszero(target) ? Q[] : nothing
    vs = flat(T, levelof(T, target), F[basis; target])
    solve_columns(vs[1:(end - 1)], vs[end])
end

function add_level!(T::Tower, kind::Symbol, arg, dtheta, seq::Int)
    K = T.Ts[end]
    push!(T.levels, Level(kind, arg, dtheta, seq))
    push!(T.Ts, Frac{UPoly{K}})
    nothing
end

# --- change of constant field ---------------------------------------------------
# For a field embedding φ : C -> C′ (e.g. ℚ -> ℚ(√d)), `change_constants(T, C′, φ)` builds
# the same tower over C′: same generators, with every argument and every Dθᵢ mapped by φ.
# `change_constants(T, T′, f, φ)` maps an element of T to the element of T′ with every base
# coefficient (numerators AND denominators, at every level) replaced by its image.
#
# Because φ is a field embedding that fixes x and the θᵢ, it commutes with the derivation:
#   D′(φ f) = φ(D f).
# This is what makes it legitimate to do a sub-computation (a gcd, a residue) over C′ and
# read the answer back. φ must be injective and multiplicative: a map that is only ℚ-linear
# (e.g. "take the √d-component") is NOT allowed here, since it does not respect fractions.
function change_constants(T::Tower, ::Type{C2}, φ) where {C2}
    T2 = Tower(C2, T.xk, copy(T.scales), copy(T.consts))
    T2.nexp = T.nexp
    for lv in T.levels
        j = length(T2.levels)                        # Kⱼ = coefficient field of this level
        arg2 = map_constants(T, T2, lv.arg, φ, levelof(T, lv.arg))
        K2 = T2.Ts[j + 1]
        dθ2 = UPoly{K2}(K2[map_constants(T, T2, c, φ, j) for c in lv.dtheta.c])
        add_level!(T2, lv.kind, arg2, dθ2, lv.seq)
    end
    T2
end
change_constants(T::Tower, T2::Tower, f, φ) = map_constants(T, T2, f, φ, levelof(T, f))

function map_constants(T::Tower, T2::Tower, f, φ, i::Int)
    if i == 0
        C2 = ctype(T2)
        P2 = UPoly{C2}
        return frac(P2(C2[φ(c) for c in f.num.c]), P2(C2[φ(c) for c in f.den.c]))
    end
    K2 = T2.Ts[i]                                    # type of K′ᵢ₋₁
    pm(p) = UPoly{K2}(K2[map_constants(T, T2, c, φ, i - 1) for c in p.c])
    frac(pm(f.num), pm(f.den))
end

# --- exp and log of tower elements --------------------------------------------
# Structure theorem (Risch): exp(u) is not new iff  u' = Σ ρᵢ bᵢ'  with ρ ∈ ℚ, where bᵢ is the
# argument of an exp level and θᵢ of a log level; then  u = Σ ρᵢ bᵢ + c  with c a constant
# (D c = 0), and  exp(u) = exp(c) Π θᵢ^ρᵢ (exp levels) Π argᵢ^ρᵢ (log levels). exp(c) is
# found in the constant field (`const_exp`), which may ask for a new constant generator.
function make_exp(T::Tower, u)
    c = dconst_value(T, u)
    if c !== nothing
        iszero(c) && return one(T.Ts[1])
        return lconst(T, const_exp(T, c), 0)
    end
    top = length(T.levels)
    u = liftto(T, u, top)
    K = T.Ts[end]
    basis = K[]
    for (i, lv) in enumerate(T.levels)
        push!(basis, lv.kind === :exp ? liftto(T, lv.arg, top) : liftto(T, theta(T, i), top))
    end
    dbasis = K[D(T, top, b) for b in basis]
    r = solve_relation(T, D(T, top, u), dbasis)
    if r !== nothing
        off = u
        for (ρ, b) in zip(r, basis)
            iszero(ρ) || (off = off - lq(T, ρ, top) * b)
        end
        cv = dconst_value(T, off)
        cv === nothing && throw(RischError("inconsistent exponential relation (offset not constant)"))
        res = iszero(cv) ? one(K) : lconst(T, const_exp(T, cv), top)
        for (i, lv) in enumerate(T.levels)
            ρ = r[i]
            iszero(ρ) && continue
            if lv.kind === :exp
                denominator(ρ) == 1 || throw(Restart(lv.seq, Int(denominator(ρ))))
                res = res * liftto(T, theta(T, i), top)^Int(numerator(ρ))
            else
                denominator(ρ) == 1 || throw(RischNotImplemented(
                    "exp of a rational multiple of a logarithm is an algebraic (radical) function"))
                res = res * liftto(T, lv.arg, top)^Int(numerator(ρ))
            end
        end
        return res
    end
    seq = (T.nexp += 1)
    s = get(T.scales, seq, 1)
    arg = s == 1 ? u : u * lq(T, Q(1) // s, top)
    add_level!(T, :exp, arg, UPoly{K}(K[zero(K), D(T, top, arg)]), seq)
    th = theta(T, top + 1)
    s == 1 ? th : th^s
end

function make_log(T::Tower, u)
    c = dconst_value(T, u)
    if c !== nothing
        isone(c) && return zero(T.Ts[1])
        return lconst(T, const_log(T, c), 0)
    end
    top = length(T.levels)
    u = liftto(T, u, top)
    K = T.Ts[end]
    w = D(T, top, u) / u
    basis = K[]
    for (i, lv) in enumerate(T.levels)
        push!(basis, lv.kind === :exp ? liftto(T, D(T, i - 1, lv.arg), top) :
                                        liftto(T, lv.dtheta.c[1], top))
    end
    r = solve_relation(T, w, basis)
    if r !== nothing
        # u^q = c * prod(...)  with c a constant; log u = sum r_i * (log of generator i) + log c / q
        q = reduce(lcm, denominator.(r); init = big(1))
        R = u^Int(q)
        res = zero(T.Ts[1])
        for (i, lv) in enumerate(T.levels)
            ρ = r[i]
            iszero(ρ) && continue
            e = Int(numerator(ρ * q))
            if lv.kind === :exp
                R = R / liftto(T, theta(T, i), top)^e
                res = liftto(T, res, top) + lq(T, ρ, top) * liftto(T, lv.arg, top)
            else
                R = R / liftto(T, lv.arg, top)^e
                res = liftto(T, res, top) + lq(T, ρ, top) * liftto(T, theta(T, i), top)
            end
        end
        cv = dconst_value(T, R)
        cv === nothing && throw(RischError("inconsistent logarithmic relation (not a constant ratio)"))
        res = liftto(T, res, top)
        # u^q = cv · Π(...): log u = Σ ρᵢ (log of generator i) + log(cv)/q. A ratio of -1 keeps the
        # behaviour from before Step 6 (the constant log(-1) = iπ is dropped).
        if !(isone(cv) || isone(-cv))
            res = res + lconst(T, const_log(T, cv) / cfromQ(ctype(T), Q(q)), top)
        end
        return res
    end
    add_level!(T, :log, u, UPoly{K}(K[w]), 0)
    theta(T, top + 1)
end

# --- constants: exp and log in the constant field ℚ(t₁, …, tₖ) (Step 6) -----------
# Generators (T.consts): at most one exp constant tₑ = exp(1/s), always first; and one
# log p per prime p (log r = Σ v_p(r) log p for r ∈ ℚ₊). A constant that needs a generator
# that is not there yet throws NewConstants with the extended list; `build_tower` re-parses.
struct NewConstants <: Exception
    consts::Vector{ConstGen}
end
struct NeedComplex <: Exception end            # trig input: re-parse over ℚ(i) (Step 7)

# the imaginary unit of a constant field that contains it
cimag(::Type{QI}) = QI(Q(0), Q(1))
cimag(::Type{QSB{d,B}}) where {d,B} = QSB{d,B}(cimag(B), zero(B))
cimag(::Type{Frac{UPoly{B}}}) where {B} = kconst(cimag(B))
cimag(::Type{T}) where {T} = throw(RischNotImplemented("the constant field $T does not contain i"))
is_complex_field(::Type{C}) where {C} = C === QI || C <: QSB{<:Any,QI} || (C <: Frac && cbase(C) === QI)
const MAX_CONSTS = 8

# the value of c at depth `d` of the nested constant field, if c lies in that subfield
function const_below(c, d::Int)
    while cdepth(typeof(c)) > d
        (isone(c.den) && degree(c.num) <= 0) || return nothing
        c = isempty(c.num.c) ? zero(eltype(c.num.c)) : c.num.c[1]
    end
    c
end

# exp(c) ∈ C for c = a + Σ r_p log p (a, r_p ∈ ℚ, r_p integers), else RischNotImplemented
function const_exp(T::Tower, c)
    C = ctype(T)
    gens = T.consts
    (C === Q || C === QI || C <: Frac) || throw(RischNotImplemented(
        "exp of the constant $c over the constant field $C is not implemented"))
    cx = is_complex_field(C)
    logs = [j for j in eachindex(gens) if gens[j].kind === :log]
    # c = a + b·i + Σ r_p log p  (the i column only over ℚ(i))
    cols = C[one(C); (cx ? C[cimag(C)] : C[]); C[tgen(C, j) for j in logs]; c]
    vs = cflat_all(C, cols)
    sol = solve_columns(vs[1:(end - 1)], vs[end])
    sol === nothing && throw(RischNotImplemented(
        "exp of the constant $c: only exp(a + b·i + integer multiples of logs of rationals), a, b ∈ ℚ, is implemented"))
    a = sol[1]
    b = cx ? sol[2] : Q(0)
    val = one(C)
    for (j, ρ) in zip(logs, sol[(cx ? 3 : 2):end])
        iszero(ρ) && continue
        isone(denominator(ρ)) || throw(RischNotImplemented(
            "exp of a rational multiple of log $(gens[j].arg) is an algebraic number"))
        val = val * cfromQ(C, gens[j].arg^Int(numerator(ρ)))
    end
    for r in (a, b)                         # a float that was rationalized would ask for e^(1/10¹⁶)
        denominator(r) <= MAX_CONST_DEN || throw(RischNotImplemented(
            "exp of a constant with a large denominator ($r): an inexact (floating-point) constant?"))
    end
    iszero(a) || (val = val * const_gen_power(T, :exp, a))
    iszero(b) || (val = val * const_gen_power(T, :expi, b))
    val
end
const MAX_CONST_DEN = 1000

# e^a (kind :exp) or e^(i·a) (kind :expi) as a power of the generator g = e^(1/s) or e^(i/s);
# throws NewConstants to add it (exp first, expi right after it) or to refine s
function const_gen_power(T::Tower, kind::Symbol, a::Q)
    gens = T.consts
    j = findfirst(g -> g.kind === kind, gens)
    if j === nothing
        g2 = copy(gens)
        pos = kind === :exp ? 1 : ((!isempty(gens) && gens[1].kind === :exp) ? 2 : 1)
        insert!(g2, pos, ConstGen(kind, Q(1) // denominator(a)))
        throw(NewConstants(g2))
    end
    s = denominator(gens[j].arg)
    m = a * s
    if !isone(denominator(m))                               # refine: generator e^(1/lcm(s, den a))
        g2 = copy(gens)
        g2[j] = ConstGen(kind, Q(1) // lcm(s, denominator(a)))
        throw(NewConstants(g2))
    end
    tgen(ctype(T), j)^Int(numerator(m))
end

is_monomial(p::UPoly) = count(!iszero, p.c) == 1

# log(c) ∈ C for c = r · tₑ^m with r ∈ ℚ, r > 0, m ∈ ℤ, else RischNotImplemented
function const_log(T::Tower, c)
    C = ctype(T)
    gens = T.consts
    (C === Q || C === QI || C <: Frac) || throw(RischNotImplemented(
        "log of the constant $c over the constant field $C is not implemented"))
    r, m = crational(c), 0
    if r === nothing
        jE = findfirst(g -> g.kind === :exp, gens)
        c1 = jE == 1 ? const_below(c, 1) : nothing         # c ∈ ℚ(tₑ)?
        (c1 !== nothing && is_monomial(c1.num) && is_monomial(c1.den)) || throw(RischNotImplemented(
            "log of the constant $c: only logs of rationals times powers of e are implemented"))
        r = lc(c1.num)
        m = degree(c1.num) - degree(c1.den)
    end
    r > 0 || throw(RischNotImplemented("log of the negative constant $r is complex"))
    val = m == 0 ? zero(C) : cfromQ(C, m * gens[1].arg)       # log(tₑ^m) = m/s
    missing_ = ConstGen[]
    for (n, sgn) in ((numerator(r), 1), (denominator(r), -1))
        for (p, k) in factorint(n)
            p < big(10)^12 || throw(RischNotImplemented(
                "log of a rational with a large factor that could not be factored ($p)"))
            g = ConstGen(:log, Q(p))
            j = findfirst(==(g), gens)
            if j === nothing
                push!(missing_, g)
            elseif isempty(missing_)
                val = val + (sgn * k) * tgen(C, j)
            end
        end
    end
    isempty(missing_) || throw(NewConstants(ConstGen[gens; missing_]))
    val
end

# --- term -> tower element ----------------------------------------------------
function unify(T::Tower, a, b)
    j = max(levelof(T, a), levelof(T, b))
    liftto(T, a, j), liftto(T, b, j)
end
function fold_op(T::Tower, op, els)
    acc = els[1]
    for e in els[2:end]
        a, b = unify(T, acc, e)
        acc = op(a, b)
    end
    acc
end

# The constant e, however the package prints it: Julia's ℯ, SymEngine's `E`, or
# `exp(1)` (SymEngine builds exp(u) as the power E^u).
is_e_const(t) = !safe_iscall(t) && string(t) in ("ℯ", "E", "exp(1)")

const ALGEBRAIC = (:sqrt, :cbrt)
const TRIG = (:sin, :cos, :tan, :atan, :abs)

function parse_tower(t, T::Tower)
    if T.subst !== nothing                     # Step 10: x ↦ φ(t), radicals ↦ powers of t
        r = T.subst(t, T)
        r === nothing || return r
    end
    if safe_iscall(t)
        args = arguments(t)
        if !isempty(args)
            n = opname(operation(t))
            if n in (:sin, :cos, :tan) && length(args) == 1     # Step 7: θ = exp(i·u) over ℚ(i)
                C = ctype(T)
                is_complex_field(C) || throw(NeedComplex())
                u = parse_tower(args[1], T)
                ci = cimag(C)
                E = make_exp(T, u * lconst(T, ci, levelof(T, u)))
                l = levelof(T, E)
                s2i = E - inv(E)                                 # 2i sin u
                c2 = E + inv(E)                                  # 2 cos u
                n === :sin && return s2i * lconst(T, inv(ci + ci), l)
                n === :cos && return c2 * lconst(T, inv(cfromQ(C, Q(2))), l)
                return s2i / (c2 * lconst(T, ci, l))             # tan = sin/cos
            end
            n in TRIG && throw(RischNotImplemented(
                "`$n` is not supported: only sin, cos and tan of tower elements are"))
            n in ALGEBRAIC && throw(RischNotImplemented(
                "`$n` is an algebraic (radical) function; only transcendental towers are supported"))
            if n === :^ && length(args) == 2 && is_e_const(args[1])
                return make_exp(T, parse_tower(args[2], T))          # E^u = exp(u)
            end
            a = Any[parse_tower(u, T) for u in args]
            if n === :+
                return fold_op(T, +, a)
            elseif n === :-
                length(a) == 1 && return -a[1]
                rest = fold_op(T, +, a[2:end])
                x1, b1 = unify(T, a[1], rest)
                return x1 - b1
            elseif n === :*
                return fold_op(T, *, a)
            elseif n === :/ && length(a) == 2
                x1, b1 = unify(T, a[1], a[2])
                return x1 / b1
            elseif n === :inv && length(a) == 1
                return inv(a[1])
            elseif n === :exp && length(a) == 1
                return make_exp(T, a[1])
            elseif n === :log && length(a) == 1
                return make_log(T, a[1])
            elseif n in (:sinh, :cosh, :tanh) && length(a) == 1
                e1 = make_exp(T, a[1])
                e2 = make_exp(T, -a[1])
                p, m = unify(T, e1, e2)
                half = lq(T, Q(1) // 2, levelof(T, p))
                s = (p - m) * half
                c = (p + m) * half
                n === :sinh && return s
                n === :cosh && return c
                return s / c
            elseif n === :^ && length(a) == 2
                base, ex = a
                k = const_value(T, ex)
                if k !== nothing
                    kq = crational(k)
                    kq === nothing && throw(RischNotImplemented(
                        "power with the irrational constant exponent $k (needs exp(k·log u) " *
                        "over the constant field; not implemented)"))
                    isone(denominator(kq)) && abs(kq) <= 10_000 && return base^Int(numerator(kq))
                    throw(RischNotImplemented("rational power $kq is an algebraic (radical) function"))
                end
                lg = make_log(T, base)
                p, m = unify(T, ex, lg)
                return make_exp(T, p * m)
            else
                throw(RischNotImplemented("unsupported operation `$n`"))
            end
        end
    end
    string(t) == T.xk && return frac(xpoly(ctype(T)))
    is_e_const(t) && return lconst(T, const_exp(T, one(ctype(T))), 0)
    r = leaf_rational(t)
    r !== nothing && return lq(T, r, 0)
    throw(RischNotImplemented("symbol `$t` is not the integration variable; " *
                              "symbolic parameters are not supported yet"))
end

# Build the tower for `f`. A Restart (a rational multiple such as exp(x/2) after
# exp(x)) refines the generator and re-parses; the hints only ever grow. A NewConstants
# (a constant such as e or log 2 appeared) re-parses over the larger field ℚ(t₁, …, tₖ).
# `constants` fixes the constant field instead (no constant generators can then be added).
function build_tower(f, xk::String; constants::Union{Nothing,Type} = nothing, subst = nothing)
    scales = Dict{Int,Int}()
    consts = ConstGen[]
    base = Q                                   # becomes ℚ(i) when trigonometric functions appear
    for _ in 1:50
        C = constants === nothing ? cfield(length(consts), base) : constants
        T = Tower(C, xk, scales, copy(consts))
        T.subst = subst
        try
            el = parse_tower(f, T)
            return minimal(T, el)
        catch e
            if e isa Restart
                scales[e.seq] = lcm(get(scales, e.seq, 1), e.q)
            elseif e isa NewConstants
                constants === nothing || throw(RischNotImplemented(
                    "the input involves transcendental constants, but the constant field was fixed to $constants"))
                length(e.consts) <= MAX_CONSTS || throw(RischNotImplemented(
                    "more than $MAX_CONSTS transcendental constants"))
                consts = e.consts
            elseif e isa NeedComplex
                constants === nothing || throw(RischNotImplemented(
                    "trigonometric input needs the constant field ℚ(i), but it was fixed to $constants"))
                base = QI
            else
                rethrow()
            end
        end
    end
    throw(RischError("could not find a consistent exponential generator"))
end

# drop top levels that the element does not involve
function minimal(T::Tower, el)
    i = levelof(T, el)
    while i > 0 && isone(el.den) && degree(el.num) <= 0
        el = isempty(el.num.c) ? zero(T.Ts[i]) : el.num.c[1]
        i -= 1
    end
    resize!(T.levels, i)
    resize!(T.Ts, i + 1)
    T, el
end

# --- tower element -> term ----------------------------------------------------
function theta_term(b::Builder, T::Tower, i::Int)
    lv = T.levels[i]
    mk(b, lv.kind, tower_to_term(b, T, lv.arg))
end
function poly_theta_term(b::Builder, T::Tower, i::Int, p)
    iszero(p) && return b.lift(0)
    ts = Any[]
    for (k, c) in enumerate(p.c)
        iszero(c) && continue
        ct = tower_to_term(b, T, c)
        e = k - 1
        if e == 0
            push!(ts, ct)
        else
            th = theta_term(b, T, i)
            thk = e == 1 ? th : mk(b, :^, th, b.lift(e))
            push!(ts, isone(c) ? thk : mk(b, :*, ct, thk))
        end
    end
    length(ts) == 1 ? ts[1] : mk(b, :+, ts...)
end
function tower_to_term(b::Builder, T::Tower, f)
    i = levelof(T, f)
    i == 0 && return frac_term(b, f)
    n = poly_theta_term(b, T, i, f.num)
    isone(f.den) ? n : mk(b, :/, n, poly_theta_term(b, T, i, f.den))
end

function describe(T::Tower)
    b = Builder((op, args...) -> Expr(:call, nameof(op), args...), identity, Symbol(T.xk))
    join(("θ$i = " * string(theta_term(b, T, i)) for i in eachindex(T.levels)), ", ")
end

"""
    tower_derivative(f, x; build = nothing, lift = nothing)

Differentiate `f` with the tower derivation (parse -> D -> term). Mainly a test of
the Stage 2 machinery: the result must agree with the ordinary derivative.
"""
function tower_derivative(f, x; build = nothing, lift = nothing)
    T, el = build_tower(f, string(x))
    d = D(T, el)
    b = Builder(build === nothing ? auto_build(f, x) : build,
                lift === nothing ? auto_lift(f, x) : lift, x, T.consts)
    is_complex_field(ctype(T)) && return real_term(b, T, sigma_kinds(T), d)
    tower_to_term(b, T, d)
end

# ---------------------------------------------------------------------------
# Stage 4: the Risch differential equation  y' + f y = g  over C(x)
#
# Used for  ∫ a θ^j  with θ = exp(u):  y' + (j u') y = a  (Bronstein ch. 6).
# Since f = j u' is a derivative it has no simple poles, which makes the bounds
# below sound (valuations at a finite place p, with f ~ p^-m, g ~ p^-k):
#   * m >= 2 : f y dominates y', so v(y) = v(g) + m: a pole of order k - m at most;
#   * f regular at p : y' dominates when y has a pole, so v(y) = v(g) + 1: order k - 1.
#   Hence y = N/D with D built from the poles of g only.
# At infinity (a = deg f, γ = deg g): a >= 0 gives deg y = γ - a, a <= -2 gives
# deg y <= max(γ + 1, 0). The numerator N is then a polynomial of known degree
# bound, found by exact linear algebra over C (the solution is unique because the
# homogeneous solution exp(-∫f) is not rational).
# Returns y ∈ C(x), or `nothing` if there is no rational solution.
# ---------------------------------------------------------------------------
function rde_base(f::Frac{UPoly{C}}, g::Frac{UPoly{C}}) where {C}
    P = UPoly{C}
    iszero(g) && return zero(Frac{P})
    iszero(f) && throw(RischError("RDE with f = 0 is plain integration"))
    Fn, Df = f.num, f.den
    G, Dg = g.num, g.den
    a = degree(Fn) - degree(Df)
    a == -1 && return :general                          # simple pole of f at infinity (step 9c)
    # denominator bound
    Dn = one(P)
    fparts = squarefree(Df)
    for (gk, k) in squarefree(Dg)
        remaining = gk
        for (fi, i) in fparts
            part = gcd(remaining, fi)
            degree(part) > 0 || continue
            i == 1 && return :general                   # simple pole of f (step 9c)
            Dn = Dn * part^max(0, k - i)
            remaining = quo(remaining, part)
        end
        Dn = Dn * remaining^max(0, k - 1)
    end
    any(i == 1 for (_, i) in fparts) && return :general # simple poles of f elsewhere: weak normalisation
    γ = degree(G) - degree(Dg)
    nup = a >= 0 ? γ - a : max(γ + 1, 0)
    M = nup + degree(Dn)
    M < 0 && return nothing
    dD = deriv(Dn)
    mono(k) = P(C[i == k + 1 ? one(C) : zero(C) for i in 1:(k + 1)])
    cols = P[]
    for k in 0:M
        N = mono(k)
        dN = k == 0 ? zero(P) : k * mono(k - 1)
        push!(cols, Df * Dg * (Dn * dN - dD * N) + Fn * Dg * Dn * N)
    end
    target = G * Df * Dn * Dn
    len = maximum(length(p.c) for p in [cols; target])
    coords(p) = C[i <= length(p.c) ? p.c[i] : zero(C) for i in 1:len]
    sol = solve_columns([coords(p) for p in cols], coords(target))
    sol === nothing && return nothing
    y = frac(P(sol), Dn)
    dx(y) + f * y == g || throw(RischError("RDE solution failed its own check"))
    y
end

# ---------------------------------------------------------------------------
# Stage 4b: the Risch differential equation over a tower K_m = k(t), k = K_{m-1}
#
#   y' + f y = g,   f = j u' (so exp(-∫f) = θ^-j is not in K by independence)
#
# Supported shape: f and g are polynomials in t (t = log), or Laurent polynomials
# in t (t = exp); a normal denominator raises RischNotImplemented. Writing
# y = Σ cᵢ tⁱ with cᵢ ∈ k:
#   t = log(w), t' = w'/w ∈ k:   cᵢ' + f cᵢ + (i+1) cᵢ₊₁ t' = gᵢ   (f ∈ k)
#   t = exp(w):                  cᵢ' + (f + i w') cᵢ = gᵢ          (f ∈ k)
# which are RDEs in k (recursion). If f itself involves t, the leading term of f
# fixes the support of y ( deg y = deg g - deg f ), and the cᵢ follow
# algebraically from the top (or from the bottom when only negative powers of an
# exponential occur). Every candidate is verified exactly; bounds only decide
# where to look, so they can lose a solution but never invent one.
# Returns y ∈ K_m or `nothing` when there is no solution.
# ---------------------------------------------------------------------------
function laurent_of(T::Tower, m::Int, h, polynomial::Bool)
    k = T.Ts[m]
    θ = xpoly(k)
    p = degree(h.den)
    ((isone(h.den)) || (!polynomial && h.den == θ^p)) || throw(RischNotImplemented(
        "the Risch differential equation over a tower with a normal denominator " *
        "(needs the full Bronstein ch. 6 denominator bound and SPDE reduction)"))
    d = Dict{Int,k}()
    for (idx, c) in enumerate(h.num.c)
        iszero(c) || (d[idx - 1 - p] = c)
    end
    d
end

function from_laurent(T::Tower, m::Int, c::Dict)
    k = T.Ts[m]
    P = UPoly{k}
    isempty(c) && return zero(T.Ts[m + 1])
    lo, hi = minimum(keys(c)), maximum(keys(c))
    p = max(0, -lo)
    coeffs = fill(zero(k), hi + p + 1)
    for (i, ci) in c
        coeffs[i + p + 1] = ci
    end
    frac(P(coeffs), xpoly(k)^p)
end

# y' = g in K_m, y ∈ K_m with no logarithms allowed (used when f vanishes)
function integrate_const(T::Tower, m::Int, g)
    r = try
        integrate_el(T, m, g)
    catch e
        e isa NotElementary ? nothing : rethrow()
    end
    (r === nothing || !isempty(r.logs) || !isempty(r.atans) || !isempty(r.quads)) ? nothing : r.v
end

function rde(T::Tower, m::Int, f, g)
    iszero(g) && return zero(T.Ts[m + 1])
    if m == 0
        r = rde_base(f, g)
        return r === :general ? rde_general(T, 0, f, g) : r
    end
    lv = T.levels[m]
    k = T.Ts[m]
    zk = zero(k)
    islog = lv.kind === :log
    # normal denominators (or a log-level fraction): the general solver (step 9a)
    (laurent_shape(T, m, f, islog) && laurent_shape(T, m, g, islog)) || return rde_general(T, m, f, g)
    fl = laurent_of(T, m, f, islog)
    gl = laurent_of(T, m, g, islog)
    isempty(fl) && throw(RischError("RDE with f = 0 is plain integration"))
    df, ef = maximum(keys(fl)), minimum(keys(fl))
    dg, eg = maximum(keys(gl)), minimum(keys(gl))
    c = Dict{Int,k}()
    undecided = false                                     # exp case: cancellation not decided (8b)
    if islog
        tp = lv.dtheta.c[1]
        if df == 0                                        # f ∈ k: triangular system of RDEs in k
            st = logderiv_solve(T, m - 1, fl[0])
            if st isa Tuple                               # f = z'/z: (z y)' = z g (step 9b)
                yp = prim_cancel(T, m, st[2], g.num, typemax(Int) ÷ 2)
                yp isa Symbol && cancellation_undecided()
                yp === nothing && return nothing
                return frac(yp)
            end
            for i in dg:-1:0
                rhs = get(gl, i, zk) - (i + 1) * get(c, i + 1, zk) * tp
                ci = rde(T, m - 1, fl[0], rhs)
                if ci === nothing
                    st === :unknown && cancellation_undecided()
                    return nothing
                end
                iszero(ci) || (c[i] = ci)
            end
        else                                              # deg y = deg g - deg f, algebraic
            hi = dg - df
            hi < 0 && return nothing
            for s in (hi + df):-1:df
                i = s - df
                rhs = get(gl, s, zk)
                for (a, fa) in fl
                    a == df || (rhs -= fa * get(c, s - a, zk))
                end
                rhs -= D(T, m - 1, get(c, s, zk)) + (s + 1) * get(c, s + 1, zk) * tp
                c[i] = rhs / fl[df]
            end
        end
    else
        wp = D(T, m - 1, lv.arg)                          # w' for t = exp(w)
        # Cancellation exponent (step 8b): where the lowest (f polynomial) or top (only
        # non-positive powers in f) equation reads c' + (f_0 + s w') c = g_s, a nonzero
        # homogeneous solution c ∈ k lets the support of y extend to s. `cancellation_exponent`
        # decides it completely when it can; `:unknown` means a failed search is not a proof.
        # (e.g. u = x + t, t = exp(x): s = -1 with c constant, ∫ exp(x + e^x) = θ/t;
        #  u = x + log x + t: s = -1 with c = 1/x, ∫ exp(x + log x + e^x)/x = θ/(x t))
        needs_s0 = (df > 0 && ef >= 0) || (df <= 0 && ef < 0)
        s0 = needs_s0 ? cancellation_exponent(T, m, get(fl, 0, zk), wp) : nothing
        undecided = s0 === :unknown
        i0 = s0 isa Int ? s0 : nothing
        if df == 0 && ef == 0                             # f ∈ k: decoupled RDEs in k
            for i in eg:dg
                gi = get(gl, i, zk)
                iszero(gi) && continue
                fi = fl[0] + i * wp
                ci = iszero(fi) ? integrate_const(T, m - 1, gi) : rde(T, m - 1, fi, gi)
                ci === nothing && return nothing
                c[i] = ci
            end
        elseif df > 0                                     # top-down
            hi = dg - df
            lo = min(eg, 0, eg - ef)
            i0 === nothing || (lo = min(lo, i0))
            if hi < lo
                undecided && cancellation_undecided()
                return nothing
            end
            for s in (hi + df):-1:(lo + df)
                i = s - df
                rhs = get(gl, s, zk)
                for (a, fa) in fl
                    a == df || (rhs -= fa * get(c, s - a, zk))
                end
                cs = get(c, s, zk)
                iszero(cs) || (rhs -= D(T, m - 1, cs) + s * wp * cs)
                c[i] = rhs / fl[df]
            end
        else                                              # only f_a with a <= 0, ef < 0: bottom-up
            lo = eg - ef
            hi = max(dg, 0)
            i0 === nothing || (hi = max(hi, i0))
            if hi < lo
                undecided && cancellation_undecided()
                return nothing
            end
            for s in (lo + ef):(hi + ef)
                i = s - ef
                rhs = get(gl, s, zk)
                for (a, fa) in fl
                    a == ef || (rhs -= fa * get(c, s - a, zk))
                end
                cs = get(c, s, zk)
                iszero(cs) || (rhs -= D(T, m - 1, cs) + s * wp * cs)
                c[i] = rhs / fl[ef]
            end
        end
    end
    filter!(p -> !iszero(p.second), c)
    y = from_laurent(T, m, c)
    D(T, m, y) + f * y == g && return y
    undecided && cancellation_undecided()
    nothing
end

laurent_shape(T::Tower, m::Int, h, polynomial::Bool) =
    isone(h.den) || (!polynomial && h.den == xpoly(T.Ts[m])^degree(h.den))

# ---------------------------------------------------------------------------
# Step 9a: the Risch DE  y' + f y = g  in K_m = k(t) with arbitrary denominators
# (Bronstein ch. 6), when the Laurent-shaped solver above does not apply.
#   1. normal denominator (6.1): h = gcd(e, ∂e)/gcd(p, ∂p) (e = normal part of den g,
#      p = gcd(normal part of den f, e)); y = q/h gives a q' + b q = c with a = d_n h,
#      b = d_n h f - d_n Dh, c = d_n h² g, whose denominators are special (else: no solution).
#      Valid for weakly normalised f; f = j u' (all callers) has no simple normal poles.
#   2. special denominator (6.2, exp only): ν_t(q) ≥ n_t, q = r t^(n_t), clear t-powers.
#   3. degree bound (6.3) for a r' + b r = c in k[t].
#   4. SPDE (6.4): r = α h + β with h' + b̄ h = c̄, deg h ≤ M.
#   5. h: deg b̄ > 0 → top-down (6.5, no cancellation); b̄ ∈ k* → decoupled (exp) or
#      triangular (log) RDEs in k; b̄ = 0 → integration in K_m without new logarithms.
# Cancellation cases (Bronstein 6.6) are recognised, not solved: if one cannot be excluded
# and no solution is found, RischNotImplemented is raised instead of "no solution".
# The candidate is always verified exactly.
# ---------------------------------------------------------------------------
tval(p::UPoly) = iszero(p) ? typemax(Int) ÷ 2 : findfirst(c -> !iszero(c), p.c) - 1
# t-valuation of an element whose denominator is a power of t
tval(f::Frac) = iszero(f) ? typemax(Int) ÷ 2 : tval(f.num) - degree(f.den)

# (normal, special) parts of a polynomial in t: special = t^v for exp, 1 for log and the base (x)
function split_factor(T::Tower, m::Int, p::UPoly)
    (m > 0 && T.levels[m].kind === :exp) || return p, one(p)
    v = tval(p)
    st = xpoly(T.Ts[m])^v
    quo(p, st), st
end

# the element f of K_m as a polynomial in t, or nothing
as_poly(f::Frac) = isone(f.den) ? f.num : nothing

# the derivation on polynomials in the generator of level m (m = 0: d/dx on C[x])
polyD(T::Tower, m::Int, p::UPoly) = m == 0 ? deriv(p) : Dp(T, m, p)
# the coefficient field of the polynomials of level m (C at the base)
coeff_type(T::Tower, m::Int) = m == 0 ? ctype(T) : T.Ts[m]

# R(z) = res_t(d, A - z dD) ∈ K[z]: its roots are the residues of A/d at the roots of d
residue_poly(::Type{K}, d::UPoly, A::UPoly, dD::UPoly) where {K} = residue_resultant(d, A, dD)

# the simple-pole part d1 of the normal denominator of f (level m), and A with f = A/d1 + (no pole at d1)
function simple_pole_part(T::Tower, m::Int, f)
    dn, _ = split_factor(T, m, f.den)
    degree(dn) <= 0 && return nothing
    g = gcd(dn, deriv(dn))
    dstar = quo(dn, g)
    d1 = monic(quo(dstar, gcd(dstar, g)))
    degree(d1) <= 0 && return nothing
    s, _, _ = gcdex(quo(f.den, d1), d1)
    d1, rem(s * f.num, d1)
end

# positive integer roots of R ∈ k[z] (k = coefficients of level m): through the ℚ-coordinates
function positive_integer_roots(T::Tower, m::Int, R::UPoly)
    iszero(R) && throw(RischError("zero residue polynomial"))
    vs = m == 0 ? cflat_all(ctype(T), R.c) : flat(T, m - 1, R.c)
    g = zero(UPoly{Q})
    for j in eachindex(vs[1])
        g = gcd(g, UPoly{Q}(Q[v[j] for v in vs]))
    end
    degree(g) > 0 || return Int[]
    ns = Int[]
    for r in rational_roots(g)
        (isone(denominator(r)) && r > 0) || continue
        r <= 1000 || throw(RischNotImplemented("weak normalisation with a residue $r > 1000"))
        push!(ns, Int(numerator(r)))
    end
    ns
end

# Bronstein 6.1, WeakNormalizer: q ∈ k[t] such that f - Dq/q has no simple normal pole with a
# positive integer residue (then the normal-denominator bound is valid)
function weak_normalizer(T::Tower, m::Int, f)
    P = typeof(f.den)
    sp = simple_pole_part(T, m, f)
    sp === nothing && return one(P)
    d1, a = sp
    dd1 = polyD(T, m, d1)
    R = residue_poly(coeff_type(T, m), d1, a, dd1)
    q = one(P)
    for n in positive_integer_roots(T, m, R)
        q = q * gcd(a - n * dd1, d1)^n
    end
    q
end

# z ∈ k* (k = K_km) with z'/z = h: (:yes, z), :no or :unknown. Candidates as in
# `cancellation_exponent` (without w'): z = Π θᵢ^nᵢ (exp generators) Π aᵢ^nᵢ (log arguments)
# Π qⱼ^eⱼ (normal factors of the denominators of h), integer exponents; z is verified.
function logderiv_solve(T::Tower, km::Int, h)
    km < 0 && return iszero(h) ? (:yes, one(h)) : :no     # constants: z' = 0
    K = T.Ts[km + 1]
    iszero(h) && return (:yes, one(K))
    logderiv_shape_ok(T, h) || return :no
    lift(e) = liftto(T, e, km)
    cands, bases = K[], K[]
    gen_is_log = Bool[]
    for (i, lv) in enumerate(T.levels[1:km])
        if lv.kind === :exp
            push!(cands, lift(D(T, i - 1, lv.arg)))
            push!(bases, lift(theta(T, i)))
        else
            push!(cands, lift(lv.dtheta.c[1]))
            push!(bases, lift(lv.arg))
        end
        push!(gen_is_log, lv.kind === :log)
    end
    ngen = length(cands)
    qs, exact = factor_candidates(T, Any[h, gen_logderivs(T, km)...])
    for (l, q) in qs
        push!(cands, lift(D(T, l, q) / q))
        push!(bases, lift(q))
    end
    coarse = !exact
    r = solve_relation(T, lift(h), cands)
    r === nothing && return coarse ? :unknown : :no
    if !all(x -> isone(denominator(x)), r)
        return (coarse || any(gen_is_log[i] && !isone(denominator(r[i])) for i in 1:ngen)) ? :unknown : :no
    end
    z = one(K)
    for (ρ, bs) in zip(r, bases)
        iszero(ρ) || (z = z * bs^Int(numerator(ρ)))
    end
    D(T, km, z) / z == lift(h) ? (:yes, z) : :unknown
end
logderiv_status(T::Tower, km::Int, h) = (r = logderiv_solve(T, km, h); r isa Tuple ? :yes : r)

# a necessary condition for h to be a logarithmic derivative in a tower: in its top generator θ_ℓ,
# the polynomial part has degree ≤ 0 (θ'/θ = w', δq/q = (deg q) w' + proper for exp; proper for
# log; lower levels have degree 0), and at an exp level there is no θ^(-v) part
function logderiv_shape_ok(T::Tower, h)
    l = levelof(T, h)
    l == 0 && return true
    q, _ = divrem(h.num, h.den)
    degree(q) <= 0 || return false
    !(T.levels[l].kind === :exp && tval(h.den) > 0)
end

# v ∈ K_m with D v = h, where the only new logarithm allowed is κ log(u) = κ t (t = θ_m = log u):
# v, nothing (no such v) or :unknown
function integrate_poly_t(T::Tower, m::Int, h)
    r = try
        integrate_el(T, m, h)
    catch e
        e isa NotElementary && return nothing
        e isa RischNotImplemented && return :unknown
        rethrow()
    end
    # atan / quadratic terms: residues outside C, not of the form κ t' (see `integrate_log_poly`)
    (isempty(r.atans) && isempty(r.quads)) || return nothing
    v = liftto(T, r.v, m)
    tgt = zero(T.Ts[m + 1])
    for (cj, wj) in r.logs
        w = liftto(T, wj, m)
        tgt = tgt + lconst(T, cj, m) * (D(T, m, w) / w)
    end
    iszero(tgt) && return v
    T.levels[m].kind === :log || return nothing
    θ = theta(T, m)
    κ = dconst_value(T, tgt / D(T, m, θ))
    κ === nothing && return nothing
    v + lconst(T, κ, m) * θ
end

# primitive cancellation (Bronstein 6.6): h' + b h = c in k[t] (t = log u) with b = z'/z, z ∈ k*:
# (z h)' = z c, so h = (∫ z c)/z, polynomial in t of degree ≤ M. Returns h, nothing or :unknown.
function prim_cancel(T::Tower, m::Int, z, c::UPoly, M::Int)
    zm = liftto(T, z, m)
    w = integrate_poly_t(T, m, zm * frac(c))
    w isa Symbol && return w
    w === nothing && return nothing
    hq = w / zm                                         # + κ/z for any constant κ: degree 0 in t
    (isone(hq.den) && degree(hq.num) <= M) || return nothing
    hq.num
end

# SPDE (Bronstein 6.4): a q' + b q = c, deg q ≤ n, a, b, c ∈ k[t]. Returns (b̄, c̄, M, α, β):
# q = α h + β with h' + b̄ h = c̄, deg h ≤ M; or nothing (no solution).
function spde(T::Tower, m::Int, a::UPoly, b::UPoly, c::UPoly, n::Int)
    P = typeof(a)
    if n < 0
        return iszero(c) ? (zero(P), zero(P), 0, zero(P), zero(P)) : nothing
    end
    if degree(a) == 0
        ia = inv(a.c[1])
        return (scale(ia, b), scale(ia, c), n, one(P), zero(P))
    end
    g = gcd(a, b)
    if degree(g) > 0
        cq, cr = divrem(c, g)
        iszero(cr) || return nothing
        a, b, c = quo(a, g), quo(b, g), cq
        degree(a) == 0 && return spde(T, m, a, b, c, n)
    end
    s, t, _ = gcdex(b, a)                       # s b + t a = 1
    r0 = s * c
    qd, r = divrem(r0, a)                        # b r + a z = c with deg r < deg a
    z = t * c + qd * b
    res = spde(T, m, a, b + polyD(T, m, a), z - polyD(T, m, r), n - degree(a))
    res === nothing && return nothing
    b̄, c̄, M, α, β = res
    (b̄, c̄, M, a * α, a * β + r)
end

function rde_general(T::Tower, m::Int, f, g)
    # 0. weak normalisation (step 9c): y = z/q, z' + (f - Dq/q) z = g q
    q0 = weak_normalizer(T, m, f)
    if !isone(q0)
        qF = frac(q0)
        z = rde_general(T, m, f - frac(polyD(T, m, q0)) / qF, g * qF)
        return z === nothing ? nothing : z / qF
    end
    lv = m == 0 ? nothing : T.levels[m]
    islog = m == 0 || lv.kind === :log                  # the base behaves as t = x primitive over C
    k = coeff_type(T, m)
    P = UPoly{k}
    F = T.Ts[m + 1]
    t = xpoly(k)
    undecided = false
    # 1. normal denominator
    dn, _ = split_factor(T, m, f.den)
    en, _ = split_factor(T, m, g.den)
    p = gcd(dn, en)
    h = quo(gcd(en, deriv(en)), gcd(p, deriv(p)))
    hF, dnF = frac(h), frac(dn)
    aP = dn * h
    bF = dnF * hF * f - dnF * frac(polyD(T, m, h))
    cF = dnF * hF * hF * g
    nb_, _ = split_factor(T, m, bF.den)                 # denominators must be special
    degree(nb_) > 0 && throw(RischError("RDE: b has a normal denominator after the normal-denominator step"))
    nc_, _ = split_factor(T, m, cF.den)
    degree(nc_) > 0 && return nothing                   # Bronstein 6.1: then no solution exists
    # 2. special denominator
    nt = 0
    if islog
        bP, cP = bF.num, cF.num                         # denominators are 1
    else
        wp = liftto(T, D(T, m - 1, lv.arg), m)          # w' as an element of K_m
        nb, nc = tval(bF), tval(cF)
        lowq = nb < 0 ? nc - nb : min(nc, 0)
        if nb == 0
            b0 = bF.num.c[1 + degree(bF.den)]           # coefficient of t^0 (den = t^v)
            s0 = cancellation_exponent(T, m, b0 / aP.c[1], D(T, m - 1, lv.arg))
            s0 === :unknown && (undecided = true)
            s0 isa Int && (lowq = min(lowq, s0))
        end
        nt = min(0, lowq)
        tn = frac(t)^nt
        b1 = bF + lq(T, Q(nt), m) * wp * frac(aP)
        c1 = cF / tn
        N = max(0, -tval(b1), -tval(c1))
        tN = frac(t^N)
        aP = aP * t^N
        bP, cP = as_poly(b1 * tN), as_poly(c1 * tN)
        (bP === nothing || cP === nothing) && throw(RischError("RDE: special denominator not cleared"))
    end
    # 3. degree bound for a r' + b r = c
    n, und = rde_degree_bound(T, m, aP, bP, degree(cP))
    und && (undecided = true)
    # 4. SPDE, 5. solve h' + b̄ h = c̄
    y = nothing
    sp = spde(T, m, aP, bP, cP, n)
    if sp !== nothing
        b̄, c̄, M, α, β = sp
        hsol = poly_rde_reduced(T, m, b̄, c̄, M)
        if hsol isa Symbol                              # :unknown from a cancellation case
            undecided = true
        elseif hsol !== nothing
            q = α * hsol + β
            num_, den_ = q, h
            nt >= 0 ? (num_ = num_ * t^nt) : (den_ = den_ * t^(-nt))
            y = frac(num_, den_)
        end
    end
    y !== nothing && D(T, m, y) + f * y == g && return y
    undecided && cancellation_undecided()
    nothing
end

# Degree bound n for a r' + b r = c in k[t] (Bronstein 6.3), dc = deg c (step 3 of `rde_general`,
# shared with `prde`). Returns (n, undecided): undecided when a cancellation case could not be
# decided, in which case n may be too small.
function rde_degree_bound(T::Tower, m::Int, aP::UPoly, bP::UPoly, dc::Int)
    islog = m == 0 || T.levels[m].kind === :log
    k = coeff_type(T, m)
    undecided = false
    da, db = degree(aP), degree(bP)
    if islog
        if iszero(bP)                                   # a r' = c
            n = max(0, dc - da + 1)
        elseif db > da
            n = max(0, dc - db)
        elseif db < da - 1
            n = max(0, dc - da + 1)
        elseif db == da - 1                             # cancellation: -lc(b)/lc(a) = m t' + z'?
            n = max(0, dc - db)
            mm = limited_log_multiple(T, m, -lc(bP) / lc(aP))
            mm === :unknown && (undecided = true)
            mm isa Int && (n = max(n, mm))
        else                                            # db == da: -lc(b)/lc(a) = z'/z? (step 9b)
            n = max(0, dc - db)
            st = logderiv_solve(T, m - 1, -lc(bP) / lc(aP))
            if st === :unknown
                undecided = true
            elseif st isa Tuple                         # β = -[t^(da-1)](a z' + b z)/(z lc(a)) = m t' + w'?
                z = st[2]
                e = scale(D(T, m - 1, z), aP) + scale(z, bP)
                ec = da >= 1 && length(e.c) >= da ? e.c[da] : zero(k)
                mm = limited_log_multiple(T, m, -ec / (z * lc(aP)))
                mm === :unknown && (undecided = true)
                mm isa Int && (n = max(n, mm))
            end
        end
    else
        n = max(0, dc - max(da, db))
        if db == da
            s0 = cancellation_exponent(T, m, lc(bP) / lc(aP), D(T, m - 1, T.levels[m].arg))
            s0 === :unknown && (undecided = true)
            s0 isa Int && (n = max(n, s0))
        end
    end
    n, undecided
end

# h' + b h = c in k[t], deg h ≤ M; returns h, nothing (no solution) or :unknown
function poly_rde_reduced(T::Tower, m::Int, b::UPoly, c::UPoly, M::Int)
    P = typeof(b)
    k = coeff_type(T, m)
    zk = zero(k)
    iszero(c) && return zero(P)
    M < 0 && return nothing
    if m == 0 && iszero(b)                              # base: h' = c in C[x]
        h = integrate_poly(c)
        return degree(h) <= M ? h : nothing
    end
    lv = m == 0 ? nothing : T.levels[m]
    if degree(b) > 0 || m == 0                          # no cancellation (6.5); at the base also b ∈ C*
        h = zero(P)
        n = M
        while !iszero(c)
            mm = degree(c) - degree(b)
            (n < 0 || mm < 0 || mm > n) && return nothing
            cs = fill(zk, mm + 1)
            cs[mm + 1] = lc(c) / lc(b)
            pq = P(cs)
            h = h + pq
            n = mm - 1
            c = c - polyD(T, m, pq) - b * pq
        end
        return h
    end
    if iszero(b)                                        # h' = c: no new logarithms (log: κ t allowed)
        v = lv.kind === :log ? integrate_poly_t(T, m, frac(c)) : integrate_const(T, m, frac(c))
        v isa Symbol && return v
        (v === nothing || !isone(v.den) || degree(v.num) > M) && return nothing
        return v.num
    end
    b0 = b.c[1]                                         # b ∈ k*
    degree(c) > M && return nothing
    cs = fill(zk, M + 1)
    if lv.kind === :exp                                 # decoupled: h_i' + (b + i w') h_i = c_i
        wp = D(T, m - 1, lv.arg)
        for i in 0:M
            ci = i + 1 <= length(c.c) ? c.c[i + 1] : zk
            iszero(ci) && continue
            fi = b0 + i * wp
            hi = iszero(fi) ? integrate_const(T, m - 1, ci) : rde(T, m - 1, fi, ci)
            hi === nothing && return nothing
            cs[i + 1] = hi
        end
        return P(cs)
    end
    # log: b = z'/z → (z h)' = z c (step 9b); else triangular, h_i' + b h_i = c_i - (i+1) h_(i+1) t'
    st = logderiv_solve(T, m - 1, b0)
    st isa Tuple && return prim_cancel(T, m, st[2], c, M)
    tp = lv.dtheta.c[1]
    for i in M:-1:0
        ci = i + 1 <= length(c.c) ? c.c[i + 1] : zk
        rhs = i + 1 <= M ? ci - (i + 1) * cs[i + 2] * tp : ci
        hi = iszero(rhs) ? zk : rde(T, m - 1, b0, rhs)
        if hi === nothing
            return st === :no ? nothing : :unknown
        end
        cs[i + 1] = hi
    end
    P(cs)
end

# -lc(b)/lc(a) = m t' + z' with z ∈ k and m ∈ ℤ, t = log u (limited integration, Bronstein 7.2)?
# Returns the integer m, nothing (no such m) or :unknown.
function limited_log_multiple(T::Tower, m::Int, α)
    if m == 0                                           # α ∈ C, t = x: α = m·1 + w' with w' = 0
        mi = cinteger(α)
        return mi === nothing ? nothing : Int(numerator(mi))
    end
    r = try
        integrate_el(T, m - 1, α)
    catch e
        e isa NotElementary && return nothing
        e isa RischNotImplemented && return :unknown
        rethrow()
    end
    # SpecialTerm: ∫α is not elementary at all; atan / quadratic terms: residues outside C
    (isempty(r.atans) && isempty(r.quads)) || return nothing
    K = T.Ts[m]
    tgt = zero(K)
    for (cj, wj) in r.logs
        tgt = tgt + lconst(T, cj, m - 1) * (D(T, m - 1, wj) / wj)
    end
    iszero(tgt) && return 0
    cv = dconst_value(T, tgt / T.levels[m].dtheta.c[1])
    cv === nothing && return nothing
    mi = cinteger(cv)
    mi === nothing ? nothing : Int(numerator(mi))
end

cancellation_undecided() = throw(RischNotImplemented(
    "Risch DE, cancellation case: whether f₀ + s·w' is a logarithmic derivative in k could not be decided"))

# Step 8b. The integers s for which  c' + (f₀ + s w') c = 0  has a solution c ∈ k* (k = K_(m-1),
# t = θ_m = exp(w)): then -(f₀ + s w') = c'/c is a logarithmic derivative in k. Writing
# c = (constant) Π θᵢ^(nᵢ) Π qⱼ^(eⱼ) (generators of k and normal irreducible factors, all
# exponents integers), c'/c = Σ nᵢ bᵢ' + Σ eⱼ δqⱼ/qⱼ with bᵢ' the derivative of an exp argument
# or θᵢ' = aᵢ'/aᵢ of a log; the qⱼ show up in the denominators of f₀ and w'. So solve
#     f₀ = Σ ρᵢ (candidates) - s w'     over ℚ.
# w' is not in the span of logarithmic derivatives (t is a monomial over k), so s is unique:
# a non-integer s means no cancellation. The factor list (squarefree factors, split by rational
# roots at the base) can be too coarse; in that case the answer is :unknown, never a guess.
# Returns an Int, `nothing` (no cancellation) or :unknown.
function cancellation_exponent(T::Tower, m::Int, f0, wp)
    km = m - 1
    # s w' cannot change the top-level shape of f0 when f0 lies higher than w'
    (levelof(T, f0) > levelof(T, wp) && !logderiv_shape_ok(T, f0)) && return nothing
    K = T.Ts[m]                                         # the type of k = K_km
    lift(e) = liftto(T, e, km)
    cands = K[]
    gen_is_log = Bool[]
    for (i, lv) in enumerate(T.levels[1:km])
        push!(cands, lift(lv.kind === :exp ? D(T, i - 1, lv.arg) : lv.dtheta.c[1]))
        push!(gen_is_log, lv.kind === :log)
    end
    ngen = length(cands)
    # factors of f0, w' and of the generators' own log-derivatives (e.g. a'/a of a log), refined
    qs, exact = factor_candidates(T, Any[f0, wp, gen_logderivs(T, km)...])
    for (l, q) in qs
        push!(cands, lift(D(T, l, q) / q))
    end
    coarse = !exact
    r = solve_relation(T, lift(f0), K[cands; lift(wp)])
    r === nothing && return coarse ? :unknown : nothing
    s = -r[end]
    isone(denominator(s)) || return nothing             # unique s, not an integer
    ρ = r[1:(end - 1)]
    if !all(x -> isone(denominator(x)), ρ)
        # a non-integer exponent of an exp generator means c ∉ k; of a log argument or a factor,
        # c could still be in k (a perfect power), so do not decide
        (coarse || any(gen_is_log[i] && !isone(denominator(ρ[i])) for i in 1:ngen)) && return :unknown
        return nothing
    end
    Int(numerator(s))
end

# Normal factors (level, q) of the denominators in h (level l), at every level. At h's own top
# level the simple-pole factors are split by residue (Rothstein–Trager): q_c = gcd(d1, A - c·Dd1)
# collects the irreducible factors where h has residue c. Lower levels (coefficients of h) are
# split by rational roots at the base only. Returns `exact`: every group either has a uniform
# residue in h or is linear (irreducible); otherwise a log-derivative test using these factors
# may be incomplete, and callers answer :unknown instead of "no".
function normal_factors!(out, T::Tower, h, l::Int; top::Bool = true)
    iszero(h) && return true
    exact = true
    d, _ = split_factor(T, l, h.den)
    if degree(d) > 0
        for (p, k) in squarefree(d)
            p = monic(p)
            exact &= (top && k == 1) ? residue_split!(out, T, l, h, p) : linear_split!(out, T, l, p)
        end
    end
    if l > 0
        for c in h.num.c
            exact &= normal_factors!(out, T, c, l - 1; top = false)
        end
        for c in h.den.c
            exact &= normal_factors!(out, T, c, l - 1; top = false)
        end
    end
    exact
end

# rational-root split at the base (linear factors are irreducible); elsewhere only degree 1 is exact
function linear_split!(out, T::Tower, l::Int, p::UPoly)
    if l > 0
        push!(out, (l, frac(p)))
        return degree(p) == 1
    end
    rest = p
    CC = eltype(p.c)
    for r in constant_roots(rest)
        lin = UPoly{CC}(CC[-r, one(CC)])
        push!(out, (0, frac(lin)))
        rest = quo(rest, lin)
    end
    degree(rest) > 0 || return true
    push!(out, (0, frac(monic(rest))))
    degree(rest) == 1
end

# split the simple factor p of h's denominator (level l) by the residues of h
function residue_split!(out, T::Tower, l::Int, h, p::UPoly)
    s, _, _ = gcdex(quo(h.den, p), p)
    A = rem(s * h.num, p)
    dP = polyD(T, l, p)
    K = coeff_type(T, l)
    R = residue_poly(K, p, A, dP)
    if degree(R) <= 0
        push!(out, (l, frac(p)))
        return degree(p) == 1
    end
    Rm = monic(R)
    CT = ctype(T)
    cs = CT[]
    for c in Rm.c                                      # residues must be constants
        v = l == 0 ? c : dconst_value(T, c)
        if v === nothing
            push!(out, (l, frac(p)))
            return degree(p) == 1
        end
        push!(cs, v)
    end
    Rc = UPoly{CT}(cs)
    Rc = quo(Rc, gcd(Rc, deriv(Rc)))
    rest = p
    for c in constant_roots(Rc)
        cl = l == 0 ? c : lconst(T, c, l - 1)
        gc = gcd(rest, A - scale(cl, dP))
        degree(gc) > 0 || continue
        push!(out, (l, frac(monic(gc))))
        rest = quo(rest, gc)
    end
    degree(rest) > 0 || return true
    push!(out, (l, frac(monic(rest))))
    degree(rest) == 1
end

# the element as an element of the lowest level it lies in (inverse of `liftto`)
function unlift(T::Tower, h)
    l = levelof(T, h)
    while l > 0 && isone(h.den) && degree(h.num) <= 0
        h = isempty(h.num.c) ? zero(T.Ts[l]) : h.num.c[1]
        l -= 1
    end
    h
end

# the generators' logarithmic derivatives of K_km at their own levels (exp: b', log: a'/a)
gen_logderivs(T::Tower, km::Int) =
    Any[lv.kind === :exp ? D(T, i - 1, lv.arg) : lv.dtheta.c[1] for (i, lv) in enumerate(T.levels[1:km])]

# factors of the given elements (each at its own level), refined; and whether they are exact
function factor_candidates(T::Tower, elems)
    qs = Tuple{Int,Any}[]
    exact = true
    for e in elems
        u = unlift(T, e)
        exact &= normal_factors!(qs, T, u, levelof(T, u))
    end
    refine_factors(qs), exact
end

# common refinement of factor lists (same level): replace overlapping q, q' by gcd and cofactors
function refine_factors(qs)
    L = unique(qs)
    changed = true
    while changed
        changed = false
        for i in eachindex(L), j in (i + 1):length(L)
            (li, fi), (lj, fj) = L[i], L[j]
            li == lj || continue
            g = gcd(fi.num, fj.num)
            degree(g) > 0 || continue
            new = Tuple{Int,Any}[(li, frac(monic(g)))]
            a, b = quo(fi.num, g), quo(fj.num, g)
            degree(a) > 0 && push!(new, (li, frac(monic(a))))
            degree(b) > 0 && push!(new, (lj, frac(monic(b))))
            L = unique(vcat([L[x] for x in eachindex(L) if x != i && x != j], new))
            changed = true
            break
        end
    end
    L
end

# ---------------------------------------------------------------------------
# Step 9d: the parametric Risch DE in towers (Bronstein 7.1)
#
#   y' + f y = Σ cᵢ gᵢ,    y ∈ K_m,  c = (c₁, …, c_r) ∈ C^r unknown
#
# The solutions (y, c) form a finite-dimensional C-vector space; `prde` returns a basis
# [(y, c)] of it, or `nothing` when a case is not handled (an undecided cancellation case, a
# weak normaliser with a huge residue): callers must not conclude anything from `nothing`.
# The steps are those of `rde_general`; every condition "Σ cᵢ (something) = 0" becomes a linear
# constraint on c over C (`c_nullspace`, through the C-coordinates `cflat_c`), and the problem is
# re-parametrised on the solution space of the constraint (c = Σ c'ⱼ Nⱼ):
#   0. weak normalisation: y = z/q;
#   1. normal denominator h (every solution has normal denominator dividing h, f weakly
#      normalised); a q' + b q = Σ cᵢ Cᵢ with Cᵢ = d_n h² gᵢ;
#   2. the normal poles left in Σ cᵢ Cᵢ must cancel (constraint);
#   3. special denominator (exp: lowest power of t, with the cancellation exponent);
#   4. degree bound (`rde_degree_bound`);
#   5. parametric SPDE (`prde_spde`): q = α h + Σ c'ⱼ βⱼ with h' + b̄ h = Σ c'ⱼ C̄ⱼ;
#   6. polynomial solutions (`prde_poly`): deg b̄ > 0 top-down (linear in the right-hand sides);
#      b̄ ∈ k one coefficient of h at a time, top-down, each a parametric RDE in k (recursion)
#      whose parameters are the current solution basis (log: the coupling term -(s+1) h_(s+1) t'
#      is part of each right-hand side). This also covers b̄ = 0 (integration, where k's
#      constants are the homogeneous solutions) and the cancellation cases (the recursive call
#      returns the homogeneous solutions in k), so no logarithmic-derivative test is needed here.
# Every basis element is verified exactly.
# ---------------------------------------------------------------------------

# C-coordinates of elements of K_l (aligned across the list): C-linear relations among the
# elements are exactly those among the vectors (as `flat`, stopping at C instead of ℚ)
function cflat_c(T::Tower{C}, l::Int, elems) where {C}
    isempty(elems) && return Vector{C}[]
    L = reduce(plcm, [e.den for e in elems]; init = one(typeof(first(elems).den)))
    nums = [e.num * quo(L, e.den) for e in elems]
    n = maximum(length(p.c) for p in nums)
    K = l == 0 ? C : T.Ts[l]
    parts = [begin
                 col = K[k <= length(p.c) ? p.c[k] : zero(K) for p in nums]
                 l == 0 ? [C[c] for c in col] : cflat_c(T, l - 1, col)
             end for k in 1:n]
    [reduce(vcat, (parts[k][j] for k in 1:n); init = C[]) for j in eachindex(elems)]
end

# a basis of {c ∈ S^r : Σ cⱼ vⱼ = 0} (the vⱼ of equal length)
function nullspace_cols(vs::Vector{Vector{S}}, r::Int) where {S}
    nrow = r == 0 ? 0 : length(vs[1])
    M = S[vs[j][i] for i in 1:nrow, j in 1:r]
    piv = Int[]
    row = 1
    for col in 1:r
        row > nrow && break
        p = findfirst(i -> !iszero(M[i, col]), row:nrow)
        p === nothing && continue
        p += row - 1
        if p != row
            for j in 1:r
                M[row, j], M[p, j] = M[p, j], M[row, j]
            end
        end
        pv = inv(M[row, col])
        for j in 1:r
            M[row, j] = M[row, j] * pv
        end
        for i in 1:nrow
            (i == row || iszero(M[i, col])) && continue
            fct = M[i, col]
            for j in 1:r
                M[i, j] = M[i, j] - fct * M[row, j]
            end
        end
        push!(piv, col)
        row += 1
    end
    basis = Vector{S}[]
    for fc in 1:r
        fc in piv && continue
        v = fill(zero(S), r)
        v[fc] = one(S)
        for (i, pc) in enumerate(piv)
            v[pc] = -M[i, fc]
        end
        push!(basis, v)
    end
    basis
end

# a basis of the c ∈ C^r with Σ cᵢ eᵢ = 0, eᵢ elements of K_l
function c_nullspace(T::Tower{C}, l::Int, elems) where {C}
    r = length(elems)
    all(iszero, elems) && return [C[i == j ? one(C) : zero(C) for i in 1:r] for j in 1:r]
    nullspace_cols(cflat_c(T, l, elems), r)
end

# Σ cᵢ eᵢ for constants cᵢ ∈ C: elements of K_l, and polynomials over the coefficients of level m
function ccomb(T::Tower, l::Int, c, es)
    s = zero(T.Ts[l + 1])
    for (ci, e) in zip(c, es)
        iszero(ci) || (s = s + lconst(T, ci, l) * e)
    end
    s
end
function ccomb_poly(T::Tower, m::Int, c, ps, ::Type{P}) where {P}
    s = zero(P)
    for (ci, p) in zip(c, ps)
        iszero(ci) || (s = s + scale(m == 0 ? ci : lconst(T, ci, m - 1), p))
    end
    s
end
# Σ_j c'ⱼ Nⱼ ∈ C^r: the original parameters from those of a re-parametrisation
function cback(T::Tower{C}, N, cp, r::Int) where {C}
    v = fill(zero(C), r)
    for (j, cj) in enumerate(cp)
        iszero(cj) && continue
        for i in 1:r
            v[i] = v[i] + cj * N[j][i]
        end
    end
    v
end

function prde(T::Tower, m::Int, f, G::Vector; normalized::Bool = false)
    C = ctype(T)
    r = length(G)
    F = T.Ts[m + 1]
    # 0. weak normalisation: y = z/q, z' + (f - Dq/q) z = Σ cᵢ q gᵢ
    if !normalized
        q0 = try
            weak_normalizer(T, m, f)
        catch e
            e isa RischNotImplemented ? nothing : rethrow()
        end
        q0 === nothing && return nothing
        if !isone(q0)
            qF = frac(q0)
            sols = prde(T, m, f - frac(polyD(T, m, q0)) / qF, Any[g * qF for g in G]; normalized = true)
            return sols === nothing ? nothing : [(y / qF, c) for (y, c) in sols]
        end
    end
    lv = m == 0 ? nothing : T.levels[m]
    islog = m == 0 || lv.kind === :log                  # the base behaves as t = x primitive over C
    k = coeff_type(T, m)
    P = UPoly{k}
    t = xpoly(k)
    # 1. normal denominator
    dn, _ = split_factor(T, m, f.den)
    en = one(P)
    for g in G
        en = plcm(en, split_factor(T, m, g.den)[1])
    end
    p = gcd(dn, en)
    h = quo(gcd(en, deriv(en)), gcd(p, deriv(p)))
    hF, dnF = frac(h), frac(dn)
    aP = dn * h
    bF = dnF * hF * f - dnF * frac(polyD(T, m, h))
    CF = Any[dnF * hF * hF * g for g in G]
    degree(split_factor(T, m, bF.den)[1]) > 0 && return nothing   # f was not weakly normalised
    # 2. the normal poles left in Σ cᵢ Cᵢ must cancel: Cᵢ = Xᵢ/(d S), constraint Σ cᵢ rem(Xᵢ, d) = 0
    dN, sN = one(P), one(P)
    for c in CF
        nd, sd = split_factor(T, m, c.den)
        dN, sN = plcm(dN, nd), plcm(sN, sd)
    end
    N1 = nothing
    if degree(dN) > 0
        X = [c.num * quo(dN * sN, c.den) for c in CF]
        N1 = c_nullspace(T, m, Any[frac(rem(x, dN)) for x in X])
        Cq = Any[frac(quo(x, dN), sN) for x in X]
        CF = Any[ccomb(T, m, v, Cq) for v in N1]
    end
    # 3. special denominator
    nt = 0
    if islog
        bP, CP = bF.num, P[c.num for c in CF]           # denominators are 1
    else
        wp = liftto(T, D(T, m - 1, lv.arg), m)
        nb = tval(bF)
        nc = minimum((tval(c) for c in CF); init = typemax(Int) ÷ 2)
        lowq = nb < 0 ? nc - nb : min(nc, 0)
        if nb == 0
            b0 = bF.num.c[1 + degree(bF.den)]           # coefficient of t^0 (den = t^v)
            s0 = cancellation_exponent(T, m, b0 / aP.c[1], D(T, m - 1, lv.arg))
            s0 === :unknown && return nothing
            s0 isa Int && (lowq = min(lowq, s0))
        end
        nt = min(0, lowq)
        tn = frac(t)^nt
        b1 = bF + lq(T, Q(nt), m) * wp * frac(aP)
        C1 = Any[c / tn for c in CF]
        Nt = max(0, -tval(b1), maximum((-tval(c) for c in C1); init = 0))
        tN = frac(t^Nt)
        aP = aP * t^Nt
        bP = as_poly(b1 * tN)
        CPs = [as_poly(c * tN) for c in C1]
        (bP === nothing || any(isnothing, CPs)) && throw(RischError("parametric RDE: special denominator not cleared"))
        CP = P[c for c in CPs]
    end
    # 4. degree bound
    n, undecided = rde_degree_bound(T, m, aP, bP, maximum(degree, CP; init = -1))
    undecided && return nothing
    # 5. parametric SPDE, 6. polynomial solutions
    b̄, C̄, M, α, β, N2 = prde_spde(T, m, aP, bP, CP, n)
    hs = prde_poly(T, m, b̄, C̄, M)
    hs === nothing && return nothing
    out = Tuple{F,Vector{C}}[]
    for (hh, c2) in hs
        q = α * hh + ccomb_poly(T, m, c2, β, P)
        c1 = cback(T, N2, c2, length(CP))
        c = N1 === nothing ? c1 : cback(T, N1, c1, r)
        num_, den_ = q, h
        nt >= 0 ? (num_ = num_ * t^nt) : (den_ = den_ * t^(-nt))
        y = frac(num_, den_)
        D(T, m, y) + f * y == ccomb(T, m, c, G) ||
            throw(RischError("parametric RDE solution failed its own check"))
        push!(out, (y, c))
    end
    out
end

# parametric SPDE (Bronstein 7.1): a q' + b q = Σ cᵢ Cᵢ, deg q ≤ n, a, b, Cᵢ ∈ k[t].
# Returns (b̄, C̄, M, α, β, N): for c = Σⱼ c'ⱼ Nⱼ (N a basis of the admissible c),
# q = α h + Σⱼ c'ⱼ βⱼ where h' + b̄ h = Σⱼ c'ⱼ C̄ⱼ and deg h ≤ M (M < 0: h = 0).
function prde_spde(T::Tower, m::Int, a::P, b::P, Cs::Vector, n::Int) where {P<:UPoly}
    C = ctype(T)
    r = length(Cs)
    if n < 0                                            # q = 0: Σ cᵢ Cᵢ = 0
        N = c_nullspace(T, m, Any[frac(c) for c in Cs])
        return (zero(P), P[zero(P) for _ in N], -1, zero(P), P[zero(P) for _ in N], N)
    end
    if degree(a) == 0
        ia = inv(a.c[1])
        ident = [C[i == j ? one(C) : zero(C) for i in 1:r] for j in 1:r]
        return (scale(ia, b), P[scale(ia, c) for c in Cs], n, one(P), P[zero(P) for _ in 1:r], ident)
    end
    g = gcd(a, b)
    if degree(g) > 0                                    # g must divide Σ cᵢ Cᵢ
        qr = [divrem(c, g) for c in Cs]
        N = c_nullspace(T, m, Any[frac(x[2]) for x in qr])
        Cs2 = P[ccomb_poly(T, m, v, [x[1] for x in qr], P) for v in N]
        b̄, C̄, M, α, β, N2 = prde_spde(T, m, quo(a, g), quo(b, g), Cs2, n)
        return (b̄, C̄, M, α, β, [cback(T, N, v, r) for v in N2])
    end
    s, tt, _ = gcdex(b, a)                              # s b + tt a = 1
    rs, zs = P[], P[]
    for c in Cs                                         # b rᵢ + a zᵢ = Cᵢ, deg rᵢ < deg a
        qd, rr = divrem(s * c, a)
        push!(rs, rr)
        push!(zs, tt * c + qd * b)
    end
    b̄, C̄, M, α, β, N = prde_spde(T, m, a, b + polyD(T, m, a),
                                 P[z - polyD(T, m, rr) for (z, rr) in zip(zs, rs)], n - degree(a))
    # q = a h + Σ cᵢ rᵢ with c = Σⱼ c'ⱼ Nⱼ
    βn = P[a * β[j] + ccomb_poly(T, m, N[j], rs, P) for j in eachindex(N)]
    (b̄, C̄, M, a * α, βn, N)
end

# h' + b h = Σ cⱼ Cⱼ in k[t] with deg h ≤ M: a basis [(h, c)] of the solutions, or nothing
function prde_poly(T::Tower, m::Int, b::P, Cs::Vector, M::Int) where {P<:UPoly}
    C = ctype(T)
    r = length(Cs)
    k = coeff_type(T, m)
    zk = zero(k)
    M < 0 && return [(zero(P), v) for v in c_nullspace(T, m, Any[frac(c) for c in Cs])]
    above(p) = frac(P(k[j > M + 1 ? p.c[j] : zk for j in 1:length(p.c)]))   # terms of degree > M
    if degree(b) > 0 || (m == 0 && !iszero(b))          # no cancellation: L(tˢ) has degree s + deg b
        db, lb = degree(b), lc(b)
        hs = P[zero(P) for _ in 1:r]
        res = P[c for c in Cs]
        for s in M:-1:0, i in 1:r
            co = s + db + 1 <= length(res[i].c) ? res[i].c[s + db + 1] : zk
            iszero(co) && continue
            mono = P(k[j == s + 1 ? co / lb : zk for j in 1:(s + 1)])
            hs[i] = hs[i] + mono
            res[i] = res[i] - polyD(T, m, mono) - b * mono
        end
        return [(ccomb_poly(T, m, v, hs, P), v) for v in c_nullspace(T, m, Any[frac(x) for x in res])]
    end
    if m == 0                                           # h' = Σ cⱼ Cⱼ in C[x], plus the constants
        hs = P[integrate_poly(c) for c in Cs]
        out = [(ccomb_poly(T, 0, v, hs, P), v) for v in c_nullspace(T, 0, Any[above(h) for h in hs])]
        push!(out, (one(P), C[zero(C) for _ in 1:r]))
        return out
    end
    # b ∈ k (possibly 0): the coefficients h_s top-down, each from a parametric RDE in k whose
    # right-hand sides are those of the current basis elements
    lv = T.levels[m]
    islog = lv.kind === :log
    b0 = iszero(b) ? zk : b.c[1]
    wp = islog ? zk : D(T, m - 1, lv.arg)
    tp = islog ? lv.dtheta.c[1] : zk
    coef(p, s) = s + 1 <= length(p.c) ? p.c[s + 1] : zk
    # L(h) has degree ≤ M, so the terms of Σ cⱼ Cⱼ above M must cancel
    B = Tuple{P,Vector{C}}[(zero(P), v) for v in c_nullspace(T, m, Any[above(c) for c in Cs])]
    for s in M:-1:0
        rhs = Any[]
        for (hb, cb) in B
            e = zk
            for (ci, Ci) in zip(cb, Cs)
                iszero(ci) || (e = e + lconst(T, ci, m - 1) * coef(Ci, s))
            end
            islog && (e = e - (s + 1) * coef(hb, s + 1) * tp)
            push!(rhs, e)
        end
        sols = prde(T, m - 1, islog ? b0 : b0 + s * wp, rhs)
        sols === nothing && return nothing
        hsB = [x[1] for x in B]
        csB = [x[2] for x in B]
        B = Tuple{P,Vector{C}}[(ccomb_poly(T, m, d, hsB, P) + P(k[j == s + 1 ? y : zk for j in 1:(s + 1)]),
                                cback(T, csB, d, r)) for (y, d) in sols]
    end
    B
end

# ---------------------------------------------------------------------------
# Stage 3: integration in a monomial extension  K(θ),  K = Kᵢ₋₁
#
#   ∫ f = v + Σ cⱼ log(wⱼ) (+ Σ dⱼ atan(uⱼ) at the base level),  v, wⱼ ∈ Kᵢ, cⱼ ∈ ℚ
#        (+ quadratic-irrational pairs √d·log(…) / √e·atan(…) at any level, Stage 5b)
#
# 1. exp only: split off the special part θ^m of the denominator (Laurent terms).
# 2. Hermite reduction (generic, uses the tower derivation) -> rational part g.
# 3. Residue criterion (Bronstein Thm 5.6.1): R(z) = res_θ(D, A - z·δD) ∈ K[z]
#    must have constant roots, else the integral is not elementary.
#    Log part Σ c log gcd(D, A - c δD); for exp, ∫ v'/v has an extra term
#    -deg(v)·u (since δv/v = deg(v)·u' + proper fraction).
# 4. Polynomial part. log: top-down reduction with limited integration of the
#    leading coefficient (Bronstein 5.8). exp: the θʲ terms need the Risch
#    differential equation y' + j u' y = aⱼ  (Stage 4); only j = 0 is done here.
# ---------------------------------------------------------------------------
struct ElemIntegral{C}
    v::Any                              # rational part, element of Kᵢ
    logs::Vector{Tuple{C,Any}}          # (c, w):  c * log(w),  c ∈ C
    atans::Vector{Tuple{C,Any}}         # (c, u):  c * atan(u), u ∈ C(x) (base level only)
    quads::Vector{Any}                  # TowerQuadLog / TowerQuadAtan (C = ℚ only)
end
ElemIntegral(v, logs, atans) = ElemIntegral(v, logs, atans, Any[])

# Stage 5b: a pair of conjugate quadratic-irrational residues a, ā = α ± β√d (d squarefree)
# of a residue polynomial over ℚ, at any level of the tower. With W = gcd(D, A - a·δD) computed
# over ℚ(√d) (via `change_constants`) and split as W = U + √d V with U, V ∈ Kᵢ₋₁[θ]:
#   a log W + ā log W̄ = α log(U² - d V²) + β√d log((U + √d V)/(U - √d V))       (d > 1)
#                      = α log(U² + e V²) + β√e LogToAtan(U, √e V),  e = -d     (d < 0)
# The α-part is an ordinary log term; the other part is one of these (U, V, u tower elements):
struct TowerQuadLog             # β√d · log((U + √d V)/(U - √d V)),  d > 1
    β::Q
    d::Int
    U::Any
    V::Any
end
struct TowerQuadAtan            # c√e · atan(√e u)  (inverted = false)  or  c√e · atan(u/√e)  (true)
    c::Q
    e::Int
    u::Any
    inverted::Bool
end

# Step 7: a conjugate pair of residues a, σ_d(a) = α ± β√d (α, β ∈ ℚ(i), d > 1 squarefree) of a
# residue polynomial over ℚ(i):  a log W + σ_d(a) log σ_d(W),  kept over the tower T2 = T with
# constants ℚ(i)(√d) (σ_d: √d ↦ -√d fixes ℚ(i)). Its derivative is σ_d-invariant, i.e. in T.
struct ExtQuadPair
    T2::Any
    a::Any                 # ∈ ℚ(i)(√d)
    W::Any                 # monic in θ, element of T2 at the level it was found
end
galois_d(c::QSB{d,B}) where {d,B} = QSB{d,B}(c.a, -c.b)
qs_down(c::QSB) = iszero(c.b) ? c.a :
    throw(RischError("a constant of ℚ(i)(√d) that should lie in ℚ(i) does not"))
ext_corr(q::ExtQuadPair) = qs_down(q.a + galois_d(q.a)) * degree(q.W.num)   # 2α·deg W

# Δ = s² d with s ∈ ℚ(i) and d > 1 a squarefree integer, or nothing. If Δ = s² d, s = u + vi,
# then u² = (p + |Δ|)/(2d) and v² = (|Δ| - p)/(2d), so d is the squarefree part of 2(p ± |Δ|)
# (a negative part is absorbed into s: √(-d) = i√d).
function qi_split_sqrt(Δ::QI)
    p, q = Δ.re, Δ.im
    m = rat_sqrt(p^2 + q^2)
    m === nothing && return nothing
    for cand in (2 * (p + m), 2 * (p - m))
        iszero(cand) && continue
        _, d0 = sqfree_split(numerator(cand) * denominator(cand))
        d = abs(d0)
        (d == 1 || d > 10^9) && continue
        s = qi_sqrt(Δ / QI(Q(d), Q(0)))
        s === nothing || return Int(d), s
    end
    nothing
end

# the pair of roots of the quadratic `rest` ∈ ℚ(i)[z] as an ExtQuadPair (and its exp correction
# 2α·deg W), or nothing if the roots are not of the form α ± β√d
function ext_quad_terms(T::Tower, i::Int, A::UPoly, D::UPoly, dD::UPoly, rest::UPoly{QI})
    rest = monic(rest)
    p0, p1 = rest.c[1], rest.c[2]
    sp = qi_split_sqrt(p1 * p1 - 4 * p0)
    sp === nothing && return nothing
    dd, s = sp
    half = inv(QI(Q(2), Q(0)))
    α, β = -p1 * half, s * half
    S = QSB{dd,QI}
    φ(c) = S(c, zero(QI))
    T2 = change_constants(T, S, φ)
    K2 = T2.Ts[i]
    up(p) = UPoly{K2}(K2[change_constants(T, T2, c, φ) for c in p.c])
    a = S(α, β)
    W = gcd(up(D), up(A) - scale(lconst(T2, a, i - 1), up(dD)))
    degree(W) > 0 || return nothing
    ExtQuadPair(T2, a, frac(W))
end

# the Stage 5a terms of a rational integral, as tower terms (U, V, u ∈ K₀ = ℚ(x))
tower_quad(q::QuadLog) = TowerQuadLog(q.β, q.d, frac(q.U), frac(q.V))
tower_quad(q::QuadAtan) = TowerQuadAtan(q.c, q.e, q.u, q.inverted)

# Step T1: the real form of a quartic RootSum (R2), a RationalIntegral over ℚ(√d) in x only, as a
# tower term: its derivative is in K₀ = ℚ(x) (stored, for `check_tower`), output by `to_term`.
# It has no θ, so it adds nothing to the exp correction Σ c·deg W.
struct BaseTerms
    q::RationalIntegral
    deriv::Any
end
tower_quad(q::RationalIntegral) = BaseTerms(q, qs_down(derivative_of(q)))

# The conjugate pair of roots of the irreducible quadratic `rest` ∈ ℚ[z] as log/atan terms
# (see above), or nothing if this case is not handled. A, D, dD = δD ∈ Kᵢ₋₁[θᵢ].
function tower_quad_terms(T::Tower, i::Int, A::UPoly, D::UPoly, dD::UPoly, rest::UPoly{Q})
    rest = monic(rest)
    p0, p1 = rest.c[1], rest.c[2]
    α = -p1 / 2
    Δ = p1^2 - 4 * p0
    iszero(Δ) && return nothing
    s, d = sqfree_split(numerator(Δ) * denominator(Δ))
    (d == 1 || abs(d) > 10^9) && return nothing
    β = Q(s) / (2 * denominator(Δ))                  # roots α ± β√d
    dd = Int(d)
    S = QS{dd}
    φ(c) = cfromQ(S, c)                               # ℚ -> ℚ(√d)
    σ(c) = S(c.a, -c.b)                               # √d -> -√d
    ψ(c) = iszero(c.b) ? c.a : throw(RischError(      # back to ℚ, on σ-invariant elements
        "splitting a quadratic-residue gcd: a σ-invariant coefficient is not rational"))
    T2 = change_constants(T, S, φ)
    K, K2 = T.Ts[i], T2.Ts[i]
    up(p) = UPoly{K2}(K2[change_constants(T, T2, c, φ) for c in p.c])
    # φ commutes with the derivation, so the image of δD is δ′ of the image of D
    W = gcd(up(D), up(A) - scale(lconst(T2, S(α, β), i - 1), up(dD)))
    degree(W) > 0 || return nothing
    # W = U + √d V:  U = (W + σW)/2,  V = (W - σW)/(2√d). Both are σ-invariant, and a σ-invariant
    # element in normalised form has σ-invariant base coefficients (the normal form is unique and
    # σ preserves it), so ψ reads them back exactly.
    half = lq(T2, Q(1) // 2, i - 1)
    inv2r = lconst(T2, inv(S(Q(0), Q(2))), i - 1)
    Uc, Vc = K[], K[]
    for w in W.c
        wσ = change_constants(T2, T2, w, σ)
        push!(Uc, change_constants(T2, T, (w + wσ) * half, ψ))
        push!(Vc, change_constants(T2, T, (w - wσ) * inv2r, ψ))
    end
    U, V = UPoly{K}(Uc), UPoly{K}(Vc)
    logs = Tuple{Q,Any}[]
    quads = Any[]
    iszero(α) || push!(logs, (α, U * U - dd * (V * V)))
    if !iszero(V)
        Uf, Vf = frac(U), frac(V)
        if dd > 0
            push!(quads, TowerQuadLog(β, dd, Uf, Vf))
        elseif !iszero(U)                            # β√e LogToAtan(U, √e V) (step T2)
            e = -dd
            for u in log_to_atan_sqrt(U, V, lq(T, Q(e), i - 1))
                push!(quads, TowerQuadAtan(2 * β, e, frac(u), false))
            end
        end
    end
    logs, quads
end

# R(z) = res_θ(D, A - z·dD) ∈ K[z] (formal degree of A - z·dD: n = max(deg A, deg dD)) by evaluation
# and interpolation: deg R ≤ deg D, so R is fixed by its values at deg D + 1 points z = 0, 1, 2, …
# (j·1 in K), each a resultant over K alone; Euclid over K(z) instead normalises nested
# fractions at every step and is far slower when K is itself ℚ(i)(e)(x)…. A point where A - z·dD
# drops below degree n is skipped (the evaluated resultant then differs from R(z_j)).
function residue_resultant(D::UPoly{K}, A::UPoly{K}, dD::UPoly{K}) where {K}
    n = max(length(A.c), length(dD.c))
    ai(k) = k <= length(A.c) ? A.c[k] : zero(K)
    di(k) = k <= length(dD.c) ? dD.c[k] : zero(K)
    zs, vs = K[], K[]
    j = 0
    while length(zs) <= degree(D)
        z = j * one(K)
        j += 1
        B = UPoly{K}(K[ai(k) - z * di(k) for k in 1:n])
        length(B.c) == n || continue
        push!(zs, z)
        push!(vs, resultant(D, B))
    end
    interpolate(zs, vs)
end

# the polynomial over K through the points (zs[k], vs[k]) (Newton divided differences)
function interpolate(zs::Vector{K}, vs::Vector{K}) where {K}
    c = copy(vs)
    for l in 2:length(zs), m in length(zs):-1:l
        c[m] = (c[m] - c[m - 1]) / (zs[m] - zs[m - l + 1])
    end
    R = UPoly{K}(K[c[end]])
    for m in (length(zs) - 1):-1:1
        R = R * UPoly{K}(K[-zs[m], one(K)]) + UPoly{K}(K[c[m]])
    end
    R
end

# R(z) = res_θ(D, A - z δD) must have constant roots. Returns (logs, quads): logs are
# [(c, W)] with W = gcd(D, A - c δD) ∈ Kᵢ₋₁[θ] (also the α log(U² - dV²) terms of a quadratic
# pair: for the exp correction Σ c·deg W they count exactly like the two conjugate logs), and
# quads the TowerQuadLog / TowerQuadAtan terms of irreducible quadratic residue factors.
# Step ST (SD inside towers). The factor of D ∈ K[θ] free of the outermost constant generator t
# (C = B(t)): specialise t to two rationals (a ring map on the constants, only used to find a
# candidate), take G = gcd of the two images of D, lift it back (its constants lie in B) and accept
# it only if it divides D exactly. Returns G (monic) or nothing.
inner_field(::Type{Frac{UPoly{B}}}) where {B} = B
function tower_tfree_factor(T::Tower{C}, i::Int, D::UPoly) where {C}
    rational_tfield(C) || return nothing
    B = inner_field(C)
    cands = Any[]
    for t in (2, 3, 5, 7, 11, 13)
        length(cands) == 2 && break
        bt = cfromQ(B, Q(t))
        φ(c) = (d = peval(c.den, bt); iszero(d) ? throw(DomainError(t)) : peval(c.num, bt) / d)
        try
            Tt = change_constants(T, B, φ)
            Kt = Tt.Ts[i]
            Dt = UPoly{Kt}(Kt[map_constants(T, Tt, c, φ, i - 1) for c in D.c])
            degree(Dt) == degree(D) && push!(cands, (Tt, Dt))
        catch e
            e isa InterruptException && rethrow()     # a bad specialisation point: try the next one
        end
    end
    length(cands) == 2 || return nothing
    G = gcd(cands[1][2], cands[2][2])
    (0 < degree(G) < degree(D)) || return nothing
    K = T.Ts[i]
    GL = UPoly{K}(K[map_constants(cands[1][1], T, c, kconst, i - 1) for c in G.c])
    iszero(rem(D, GL)) ? monic(GL) : nothing
end

function residue_logs(T::Tower, i::Int, A::UPoly, D::UPoly)
    if rational_tfield(ctype(T)) && !iszero(A)
        G = tower_tfree_factor(T, i, D)
        if G !== nothing                       # A/D = A₁/G + A₂/H, residues separately (step ST)
            H, r = divrem(D, G)
            iszero(r) || throw(RischError("tower_tfree_factor: G does not divide D"))
            sH, uG, g = gcdex(H, G)
            isone(g) || throw(RischError("tower_tfree_factor: G and D/G are not coprime"))
            o1, q1 = residue_logs(T, i, rem(A * sH, G), G)
            o2, q2 = residue_logs(T, i, rem(A * uG, H), H)
            return vcat(o1, o2), vcat(q1, q2)
        end
    end
    K = T.Ts[i]
    dD = Dp(T, i, D)
    Rz = residue_resultant(D, A, dD)
    iszero(Rz) && throw(RischError("zero resultant in the residue computation"))
    CT = ctype(T)
    out = Tuple{CT,Any}[]
    quads = Any[]
    degree(Rz) <= 0 && return out, quads
    Rm = monic(Rz)
    qc = CT[]
    for c in Rm.c
        v = dconst_value(T, c)
        v === nothing && throw(NotElementary(
            "the residues of the integrand are not constants (residue criterion)"))
        push!(qc, v)
    end
    Rq = UPoly{CT}(qc)
    Rsf = quo(Rq, gcd(Rq, deriv(Rq)))
    rest = Rsf
    for a in constant_roots(Rsf)
        W = gcd(D, A - scale(lconst(T, a, i - 1), dD))
        degree(W) > 0 && push!(out, (a, W))
        rest = quo(rest, UPoly{CT}(CT[-a, one(CT)]))
    end
    if CT === Q && degree(rest) >= 2
        hard = one(rest)
        for q in (degree(rest) > 2 ? factor_Q(rest) : [rest])
            if degree(q) == 2                          # a conjugate pair in ℚ(√d) (Stage 5b)
                qt = tower_quad_terms(T, i, A, D, dD, q)
                if qt !== nothing
                    append!(out, qt[1])
                    append!(quads, qt[2])
                    continue
                end
            end
            if degree(q) == 4                          # real form with √d (step RF)
                rf = tower_quartic_real(T, i, A, D, dD, q)
                if rf !== nothing
                    push!(quads, rf)
                    continue
                end
            end
            hard = hard * q
        end
        degree(hard) > 0 && append!(quads, tower_root_sums(T, i, A, D, dD, hard))   # step RT
        rest = one(rest)
    elseif CT === QI && degree(rest) >= 2
        if degree(rest) == 2                           # a pair α ± β√d over ℚ(i) (Step 7)
            qt = ext_quad_terms(T, i, A, D, dD, rest)
            if qt !== nothing
                push!(quads, qt)
                rest = one(rest)
            end
        end
        if degree(rest) > 0                            # RootSum over ℚ(i) (step RC; no factoring)
            append!(quads, tower_root_sums(T, i, A, D, dD, rest))
            rest = one(rest)
        end
    elseif rational_tfield(CT) && degree(rest) > 0          # RootSum over ℚ(t₁, …) (step RE; no factoring)
        append!(quads, tower_root_sums(T, i, A, D, dD, rest))
        rest = one(rest)
    end
    degree(rest) > 0 && throw(RischNotImplemented(
        "the residues are algebraic constants of degree ≥ 2 over the constant field $CT " *
        "(RootSum inside towers is implemented over ℚ and ℚ(i) only)"))
    out, quads
end

# ∫ p, p ∈ K[θ], θ = log(u): returns (q ∈ K[θ], logs (c, w ∈ K), atans, quads) with
# Dq + Σ c w'/w (+ atan and quadratic terms, which only come from the constant term) = p
function integrate_log_poly(T::Tower, i::Int, p::UPoly)
    K = T.Ts[i]
    P = UPoly{K}
    Lθ = T.levels[i].dtheta.c[1]                       # u'/u
    q = zero(P)
    while degree(p) > 0
        n = degree(p)
        r = integrate_el(T, i - 1, lc(p))
        # Limited integration (step 9d): lc(p) = b' + c u'/u with b ∈ K, c ∈ C is required. An atan,
        # quadratic-irrational or ExtQuadPair term carries residues outside C, which b' (residues 0)
        # and c u'/u (residues in C) cannot produce; a SpecialTerm means ∫ lc(p) is not elementary.
        (isempty(r.atans) && isempty(r.quads)) || throw(NotElementary(
            "the integral of the coefficient of log^$n needs logarithms with residues outside the constant field"))
        tgt = zero(K)                                   # Σ cⱼ wⱼ'/wⱼ, must equal c·u'/u
        for (cj, wj) in r.logs
            tgt = tgt + lconst(T, cj, i - 1) * (D(T, i - 1, wj) / wj)
        end
        # ∫ lc(p) = r.v + c·log(u) with c a constant of the field (c ∈ C, not only ℚ:
        # e.g. ∫ e·log(x)/x needs c = e). Lθ = u'/u ≠ 0, so c = tgt/Lθ, and it must be constant.
        c = zero(ctype(T))
        if !iszero(tgt)
            cv = dconst_value(T, tgt / Lθ)
            cv === nothing && throw(NotElementary(
                "the integral of the coefficient of log^$n involves logarithms other than log(u)"))
            c = cv
        end
        coeffs = fill(zero(K), n + 2)
        coeffs[n + 2] = lconst(T, c / cfromQ(ctype(T), Q(n + 1)), i - 1)
        coeffs[n + 1] = r.v
        qn = P(coeffs)
        q = q + qn
        p = p - Dp(T, i, qn)
        degree(p) < n || throw(RischError("polynomial reduction did not lower the degree"))
    end
    logs = Tuple{ctype(T),Any}[]
    atans = Tuple{ctype(T),Any}[]
    quads = Any[]
    if !iszero(p)
        r0 = integrate_el(T, i - 1, p.c[1])
        q = q + P(K[r0.v])
        append!(logs, r0.logs)
        append!(atans, r0.atans)
        append!(quads, r0.quads)
    end
    q, logs, atans, quads
end

function integrate_el(T::Tower, i::Int, f)::ElemIntegral
    if i == 0
        res = integrate_rational(f)
        isempty(res.unresolved) || ctype(T) === Q || ctype(T) === QI || rational_tfield(ctype(T)) || throw(RischNotImplemented(
            "the logarithmic part has residues of degree > 2 over the constant field $(ctype(T))"))
        quads = Any[tower_quad(q) for q in res.quads]
        for (rest, R, Dd) in res.unresolved, rs in root_sums(rest, R, Dd, "x")    # step RT
            push!(quads, BaseRootSum(rs, rootsum_derivative(rs)))
        end
        return ElemIntegral(res.rational,
                            Tuple{ctype(T),Any}[(c, frac(w)) for (c, w) in res.logs],
                            Tuple{ctype(T),Any}[(c, u) for (c, u) in res.atans], quads)
    end
    lv = T.levels[i]
    K = T.Ts[i]
    P = UPoly{K}
    F = T.Ts[i + 1]
    iszero(f) && return ElemIntegral(zero(F), Tuple{ctype(T),Any}[], Tuple{ctype(T),Any}[])
    δ(p) = Dp(T, i, p)
    A, Dn = f.num, f.den
    laurent = Dict{Int,K}()
    addl!(j::Int, α) = (laurent[j] = get(laurent, j, zero(K)) + α)
    θ = xpoly(K)
    if lv.kind === :exp
        m = findfirst(c -> !iszero(c), Dn.c) - 1        # multiplicity of θ in D
        if m > 0
            N = quo(Dn, θ^m)
            s, t, g1 = gcdex(θ^m, N)
            isone(g1) || throw(RischError("special part: gcd(θ^m, N) != 1"))
            At = A * t                                  # f = A t/θ^m + A s/N
            for (k, α) in enumerate(At.c)
                addl!(k - 1 - m, α)
            end
            A, Dn = A * s, N
        end
    end
    g, Qp, R, Dsf = hermite_reduce(δ, A, Dn)
    for (k, α) in enumerate(Qp.c)
        addl!(k - 1, α)
    end
    logs = Tuple{ctype(T),Any}[]
    atans = Tuple{ctype(T),Any}[]
    quads = Any[]
    corr = zero(ctype(T))
    if !iszero(R)
        rl, rq = try
            residue_logs(T, i, R, Dsf)
        catch e
            sp = (e isa NotElementary && lv.kind === :log) ? special_log(T, i, R, Dsf) : nothing
            sp === nothing && rethrow()
            Tuple{ctype(T),Any}[], Any[sp]                 # li-type: c·e^p·Ei(k·log(u) + k·b) (Step 8a)
        end
        for (c, W) in rl
            push!(logs, (c, frac(W)))
            corr += c * degree(W)
        end
        for q in rq                                     # 5b ratio terms: degree 0, no correction
            q isa ExtQuadPair && (corr += ext_corr(q))
            q isa TowerRootSum && (corr += rootsum_corr(q))
            q isa TowerRealForm && (corr += q.corr)
        end
        append!(quads, rq)
    end
    v = g
    if lv.kind === :log
        maxj = maximum(keys(laurent); init = 0)
        p = P(K[get(laurent, j, zero(K)) for j in 0:maxj])
        q, lp, ap, qp = integrate_log_poly(T, i, p)
        v = v + frac(q)
        for (c, w) in lp
            push!(logs, (c, frac(P(K[w]))))
        end
        append!(atans, ap)
        append!(quads, qp)
    else
        for (j, α) in laurent                           # ∫ α θ^j = y θ^j  with  y' + j u' y = α
            (j == 0 || iszero(α)) && continue
            fj = lq(T, Q(j), i - 1) * D(T, i - 1, lv.arg)
            y = rde(T, i - 1, fj, α)
            if y === nothing                            # not elementary; try Ei / erf (Step 8a)
                sp = special_exp(T, i, j, α)
                sp === nothing && throw(NotElementary(
                    "the Risch differential equation y' + $j·u'·y = a has no solution in the coefficient field, " *
                    "so the coefficient of exp(u)^$j has no elementary integral"))
                y = sp[1]
                append!(quads, sp[2])
            end
            if j > 0
                coeffs = fill(zero(K), j + 1)
                coeffs[j + 1] = y
                v = v + frac(P(coeffs))
            else
                v = v + frac(P(K[y]), θ^(-j))
            end
        end
        a0 = get(laurent, 0, zero(K))
        if !iszero(a0)
            r0 = integrate_el(T, i - 1, a0)
            v = v + frac(P(K[r0.v]))
            for (c, w) in r0.logs
                push!(logs, (c, frac(P(K[w]))))
            end
            append!(atans, r0.atans)
            append!(quads, r0.quads)
        end
        iszero(corr) || (v = v - lconst(T, corr, i) * liftto(T, lv.arg, i))
    end
    ElemIntegral(v, logs, atans, quads)
end

# d/dx of the antiderivative, computed in the tower, must equal the integrand
function check_tower(T::Tower, L::Int, res::ElemIntegral, f)
    tot = D(T, L, liftto(T, res.v, L))
    for (c, w) in res.logs
        w = liftto(T, w, L)
        tot = tot + lconst(T, c, L) * (D(T, L, w) / w)
    end
    for (c, u) in res.atans
        du = liftto(T, dx(u) / (one(T.Ts[1]) + u * u), L)
        tot = tot + lconst(T, c, L) * du
    end
    for q in res.quads
        if q isa TowerQuadLog   # d/dx [β√d log((U+√dV)/(U-√dV))] = 2βd (V'U - U'V)/(U² - dV²)
            U, V = liftto(T, q.U, L), liftto(T, q.V, L)
            num_ = D(T, L, V) * U - D(T, L, U) * V
            tot = tot + lq(T, 2 * q.β * q.d, L) * num_ / (U * U - lq(T, Q(q.d), L) * (V * V))
        elseif q isa TowerQuadAtan  # c√e atan(√e u): c e u'/(1 + e u²);  c√e atan(u/√e): c e u'/(e + u²)
            u, e = liftto(T, q.u, L), lq(T, Q(q.e), L)
            den = q.inverted ? e + u * u : one(u) + e * u * u
            tot = tot + lq(T, q.c * q.e, L) * D(T, L, u) / den
        elseif q isa SpecialTerm || q isa BaseTerms || q isa TowerRootSum || q isa BaseRootSum ||
               q isa TowerRealForm
            # stored exact derivatives (8a, T1, RT, RF)
            tot = tot + liftto(T, q.deriv, L)
        elseif q isa ExtQuadPair    # a W'/W + σ_d(a W'/W), computed over ℚ(i)(√d), read back in T
            T2 = q.T2
            w = liftto(T2, q.W, L)
            t1 = lconst(T2, q.a, L) * (D(T2, L, w) / w)
            t2 = change_constants(T2, T2, t1, galois_d)
            tot = tot + change_constants(T2, T, t1 + t2, qs_down)
        else
            throw(RischError("unknown term $(typeof(q))"))
        end
    end
    tot == f
end

function to_term(b::Builder, T::Tower, res::ElemIntegral)
    ts = Any[]
    iszero(res.v) || push!(ts, tower_to_term(b, T, res.v))
    for (c, w) in res.logs
        l = mk(b, :log, tower_to_term(b, T, w))
        push!(ts, isone(c) ? l : mk(b, :*, cterm(b, c), l))
    end
    for (c, u) in res.atans
        l = mk(b, :atan, frac_term(b, u))
        push!(ts, isone(c) ? l : mk(b, :*, cterm(b, c), l))
    end
    for q in res.quads
        if q isa TowerQuadLog
            r = mk(b, :sqrt, b.lift(q.d))
            Ut, Vt = tower_to_term(b, T, q.U), tower_to_term(b, T, q.V)
            top = mk(b, :+, Ut, mk(b, :*, r, Vt))
            bot = mk(b, :+, Ut, mk(b, :*, b.lift(-1), r, Vt))
            l = mk(b, :log, mk(b, :/, top, bot))
            push!(ts, isone(q.β) ? mk(b, :*, r, l) : mk(b, :*, cterm(b, q.β), r, l))
        elseif q isa SpecialTerm
            push!(ts, special_out(b, q, cterm(b, q.c), z -> tower_to_term(b, T, z)))
        elseif q isa BaseTerms
            push!(ts, to_term(b, q.q))
        elseif q isa TowerRealForm
            for (c, w) in q.logs
                l = mk(b, :log, tower_to_term(b, q.T2, w))
                push!(ts, isone(c) ? l : mk(b, :*, cterm(b, c), l))
            end
            for (c, p) in q.atans
                l = mk(b, :atan, tower_to_term(b, q.T2, p))
                push!(ts, isone(c) ? l : mk(b, :*, cterm(b, c), l))
            end
        elseif q.e == 1                              # residues ±i: c·atan(u), no sqrt(1)
            l = mk(b, :atan, tower_to_term(b, T, q.u))
            push!(ts, isone(q.c) ? l : mk(b, :*, cterm(b, q.c), l))
        else
            r = mk(b, :sqrt, b.lift(q.e))
            ut = tower_to_term(b, T, q.u)
            l = mk(b, :atan, q.inverted ? mk(b, :/, ut, r) : mk(b, :*, r, ut))
            push!(ts, isone(q.c) ? mk(b, :*, r, l) : mk(b, :*, cterm(b, q.c), r, l))
        end
    end
    isempty(ts) && return b.lift(0)
    length(ts) == 1 ? ts[1] : mk(b, :+, ts...)
end

# ---------------------------------------------------------------------------
# Stage 5c: polynomial × exponential × trigonometric integrands
#
# sin, cos, sinh, cosh and exp of *linear* arguments are rewritten with complex
# exponentials, so the integrand becomes  F = Σ_λ P_λ(x) e^{λx},  P_λ ∈ ℚ(i)[x],
# λ ∈ ℚ(i) (this is the Risch algorithm in the exponential tower with the constant
# field ℚ(i), where every term is integrable: ∫ P e^{λx} = e^{λx} Σ_k (-1)^k P^(k)/λ^(k+1)).
# The antiderivative is verified exactly (G' = F in this representation) and then
# folded back to real form: conjugate pairs λ = a ± ib give e^{ax}(A cos bx + B sin bx).
# Integrands outside this class (sin(x)/x, 1/(2 + cos x), tan, ...) need the full
# ℚ(i)-tower and raise RischNotImplemented (planned: Stage 5c-ii).
# ---------------------------------------------------------------------------
const QIX = UPoly{QI}
const EP = Dict{QI,QIX}                 # λ => P  meaning  Σ P(x) e^{λx}
const QI0 = QI(Q(0), Q(0))
qi(c::Q) = QI(c, Q(0))

function ep_put!(r::EP, λ::QI, P::QIX)
    S = haskey(r, λ) ? r[λ] + P : P
    iszero(S) ? delete!(r, λ) : (r[λ] = S)
    r
end
function ep_add(f::EP, g::EP)
    r = copy(f)
    for (λ, P) in g
        ep_put!(r, λ, P)
    end
    r
end
function ep_mul(f::EP, g::EP)
    r = EP()
    for (λ1, P1) in f, (λ2, P2) in g
        ep_put!(r, λ1 + λ2, P1 * P2)
    end
    r
end
ep_scale(f::EP, c::QI) = (r = EP(); for (λ, P) in f; ep_put!(r, λ, scale(c, P)); end; r)
ep_const(c::QI) = iszero(c) ? EP() : EP(QI0 => QIX(QI[c]))
ep_one() = ep_const(qi(Q(1)))
function ep_pow(f::EP, n::Int)
    r = ep_one()
    for _ in 1:n
        r = ep_mul(r, f)
    end
    r
end
ep_deriv(f::EP) = (r = EP(); for (λ, P) in f; ep_put!(r, λ, deriv(P) + scale(λ, P)); end; r)

# constant value of an EP (frequency 0, degree 0), or nothing
function ep_constant(f::EP)
    isempty(f) && return QI0
    (length(f) == 1 && haskey(f, QI0) && degree(f[QI0]) <= 0) ? f[QI0].c[1] : nothing
end

# u = c x (linear, no constant term) -> c
function ep_linear(u::EP)
    isempty(u) && return QI0
    (length(u) == 1 && haskey(u, QI0)) || throw(RischNotImplemented(
        "the argument of exp/sin/cos must be a linear function of x for this class of integrands"))
    P = u[QI0]
    degree(P) <= 1 || throw(RischNotImplemented(
        "exp/sin/cos of a nonlinear argument: not of the form polynomial × exponential × trig (Stage 5c-ii)"))
    iszero(P.c[1]) || throw(RischNotImplemented(
        "an argument with a nonzero constant term brings in e^c, sin c or cos c as new constants (Stage 5d)"))
    length(P.c) == 2 ? P.c[2] : QI0
end
ep_expc(c::QI) = iszero(c) ? ep_one() : EP(c => QIX(QI[qi(Q(1))]))
const QI_I = QI(Q(0), Q(1))

function parse_ep(t, xk::String)::EP
    if safe_iscall(t) && !isempty(arguments(t))
        args = arguments(t)
        n = opname(operation(t))
        if n === :^ && length(args) == 2 && is_e_const(args[1])
            return ep_expc(ep_linear(parse_ep(args[2], xk)))
        end
        a = EP[parse_ep(u, xk) for u in args]
        two = qi(Q(2))
        if n === :+
            return foldl(ep_add, a; init = EP())
        elseif n === :-
            length(a) == 1 && return ep_scale(a[1], qi(Q(-1)))
            return ep_add(a[1], ep_scale(foldl(ep_add, a[2:end]; init = EP()), qi(Q(-1))))
        elseif n === :*
            return foldl(ep_mul, a; init = ep_one())
        elseif (n === :/ && length(a) == 2) || (n === :inv && length(a) == 1)
            den = ep_constant(a[end])
            (den === nothing || iszero(den)) && throw(RischNotImplemented(
                "division by a non-constant is outside polynomial × exponential × trig (Stage 5c-ii)"))
            return ep_scale(n === :inv ? ep_one() : a[1], inv(den))
        elseif n === :^ && length(a) == 2
            k = ep_constant(a[2])
            (k !== nothing && iszero(k.im) && isone(denominator(k.re)) && k.re >= 0 && k.re <= 10_000) ||
                throw(RischNotImplemented("only nonnegative integer powers are supported here"))
            return ep_pow(a[1], Int(numerator(k.re)))
        elseif n === :exp && length(a) == 1
            return ep_expc(ep_linear(a[1]))
        elseif n in (:sin, :cos) && length(a) == 1
            c = ep_linear(a[1])
            ep, em = ep_expc(QI_I * c), ep_expc(-(QI_I * c))
            n === :cos && return ep_scale(ep_add(ep, em), inv(two))
            return ep_scale(ep_add(ep, ep_scale(em, qi(Q(-1)))), inv(QI(Q(0), Q(2))))
        elseif n in (:sinh, :cosh) && length(a) == 1
            c = ep_linear(a[1])
            ep, em = ep_expc(c), ep_expc(-c)
            n === :cosh && return ep_scale(ep_add(ep, em), inv(two))
            return ep_scale(ep_add(ep, ep_scale(em, qi(Q(-1)))), inv(two))
        else
            throw(RischNotImplemented(
                "`$n` is outside polynomial × exponential × trig; the full ℚ(i)-tower is planned (Stage 5c-ii)"))
        end
    end
    string(t) == xk && return EP(QI0 => QIX(QI[QI0, qi(Q(1))]))
    r = leaf_rational(t)
    r !== nothing && return ep_const(qi(r))
    is_e_const(t) && throw(RischNotImplemented("the constant e (Stage 5d)"))
    throw(RischNotImplemented("symbol `$t` is not the integration variable"))
end

function ep_integrate(f::EP)
    r = EP()
    for (λ, P) in f
        if iszero(λ)
            c = QI[i == 1 ? QI0 : P.c[i - 1] * inv(qi(Q(i - 1))) for i in 1:(length(P.c) + 1)]
            ep_put!(r, λ, QIX(c))
        else
            il = inv(λ)
            acc, d, c = zero(QIX), P, il
            while !iszero(d)
                acc = acc + scale(c, d)
                d = deriv(d)
                c = -(c * il)
            end
            ep_put!(r, λ, acc)
        end
    end
    r
end

has_trig(t) = safe_iscall(t) && !isempty(arguments(t)) &&
              (opname(operation(t)) in (:sin, :cos, :tan) || any(has_trig, arguments(t)))

conj_poly(P::QIX) = QIX(QI[QI(c.re, -c.im) for c in P.c])

function ep_to_term(b::Builder, G::EP)
    ts = Any[]
    expfac(a::Q) = iszero(a) ? nothing :
        mk(b, :exp, isone(a) ? b.x : mk(b, :*, b.lift(num(a)), b.x))
    function times(p::CX, fac)
        iszero(p) && return nothing
        parts = Any[]
        isone(p) || push!(parts, poly_term(b, p))
        fac === nothing || push!(parts, fac)
        isempty(parts) ? b.lift(1) : length(parts) == 1 ? parts[1] : mk(b, :*, parts...)
    end
    for λ in sort(collect(keys(G)); by = z -> (z.re, z.im))
        P = G[λ]
        if iszero(λ.im)
            all(iszero(c.im) for c in P.c) || throw(RischError("non-real coefficient for a real frequency"))
            t = times(CX(Q[c.re for c in P.c]), expfac(λ.re))
            t === nothing || push!(ts, t)
        elseif λ.im > 0
            get(G, QI(λ.re, -λ.im), nothing) == conj_poly(P) ||
                throw(RischError("antiderivative is not conjugate-symmetric"))
            ea = expfac(λ.re)
            ωx = isone(λ.im) ? b.x : mk(b, :*, b.lift(num(λ.im)), b.x)
            for (p, fn) in ((CX(Q[2c.re for c in P.c]), :cos), (CX(Q[-2c.im for c in P.c]), :sin))
                t = times(p, nothing)
                t === nothing && continue
                tr = mk(b, fn, ωx)
                push!(ts, isone(p) ? (ea === nothing ? tr : mk(b, :*, ea, tr)) :
                          (ea === nothing ? mk(b, :*, t, tr) : mk(b, :*, t, ea, tr)))
            end
        end
    end
    isempty(ts) && return b.lift(0)
    length(ts) == 1 ? ts[1] : mk(b, :+, ts...)
end

function integrate_trig(f, x; build = nothing, lift = nothing, verify::Bool = true)
    F = parse_ep(f, string(x))
    G = ep_integrate(F)
    verify && ep_deriv(G) != F && throw(RischError("internal check failed (trigonometric integral)"))
    bd = Builder(build === nothing ? auto_build(f, x) : build,
                 lift === nothing ? auto_lift(f, x) : lift, x)
    ep_to_term(bd, G)
end

# ---------------------------------------------------------------------------
# Step 8a: non-elementary integrals with SpecialFunctions (on by default)
#
# Where the algorithm proves that ∫ a θ^j (θ = exp(U)) is not elementary, try instead
#     a = y' + jU'y + Σ_t c_t U'/(U - t) + Σ_l d_l θ_l^(-j) W_l'/W_l [+ k]
# (the parametric Risch DE in K_m, `prde`, step 9d), since (c e^(jt) Ei(j(U - t)))' = c θ^j U'/(U - t),
# (Ei(j W_l))' = θ^j θ_l^(-j) W_l'/W_l for W_l = U - a_l (θ_l = exp(a_l) a generator below), and,
# at the base for jU = A x² + B x + C₀,
# ∫ k θ^j = k e^E √π/(2√|A|) erf(√|A| (x + h))  (erfi for A > 0),  h = B/(2A), E = C₀ - B²/(4A).
# The shifts t are 0 and the constant values of U at the poles of a (U ≡ t modulo a normal
# factor of the denominator of a). At a log level whose residues are not constant,
# ∫ c' u^m u'/(log u + b) = c' e^(-kb) Ei(k (log u + b)), k = m + 1 (li(u^k) for b = 0).
# Each term keeps its exact derivative, so the usual checks still verify the result.
# ---------------------------------------------------------------------------
struct SpecialTerm
    fn::Symbol         # :Ei, :erf or :erfi
    c::Any             # coefficient ∈ C
    p::Any             # constant prefactor e^p, p ∈ C (output only: it cancels in the derivative)
    z::Any             # the argument (Ei), or x + h (erf/erfi): a tower element
    A::Q               # erf/erfi: the coefficient of x²
    deriv::Any         # the exact derivative of the term (tower element)
end

# U ∈ C(x) at r ∈ C, or nothing at a pole
function feval(U::Frac{UPoly{C}}, r::C) where {C}
    d = peval(U.den, r)
    iszero(d) ? nothing : peval(U.num, r) / d
end

# σ at level 0 (x real), for the real-form filters of special terms
conj0(T::Tower, f) = frac(cpconj_g(T.consts, f.num), cpconj_g(T.consts, f.den))

# ∫ α θ^j (θ = exp(U), level i) with Ei / erf terms: (y, terms) with ∫ α θ^j = y θ^j + Σ terms
function special_exp(T::Tower, i::Int, j::Int, α)
    lv = T.levels[i]
    m = i - 1
    C = ctype(T)
    cx = is_complex_field(C)
    U = liftto(T, lv.arg, m)
    dU = D(T, m, U)
    θj = theta(T, i)^j
    jq = cfromQ(C, Q(j))
    jU = lq(T, Q(j), m) * U
    # over ℚ(i) an Ei argument must be real or i·real (then it has a real form)
    skinds = nothing
    if cx && m > 0
        skinds = try
            sigma_kinds(T)
        catch e
            e isa RischNotImplemented ? nothing : rethrow()
        end
        skinds === nothing && return nothing
    end
    ok_arg(z) = !cx || (s = m == 0 ? conj0(T, z) : tconj(T, skinds, z, m); s == z || s == -z)
    # shifts t ∈ C: the values of U at the poles of α (U ≡ t modulo a normal factor), and 0
    shifts = C[zero(C)]
    if !isone(α.den)
        dn, _ = split_factor(T, m, α.den)
        sq = quo(dn, gcd(dn, deriv(dn)))
        if m == 0
            for r in constant_roots(sq)
                t = feval(U, r)
                (t === nothing || t in shifts) || push!(shifts, t)
            end
        elseif degree(sq) > 0                           # roots of res_θ(sq, U.num - z U.den), if constant
            R = residue_poly(T.Ts[m], sq, U.num, U.den)
            if degree(R) > 0
                cs = Any[dconst_value(T, c) for c in monic(R).c]
                if !any(isnothing, cs)
                    Rc = UPoly{C}(C[c for c in cs])
                    for t in constant_roots(quo(Rc, gcd(Rc, deriv(Rc))))
                        t in shifts || push!(shifts, t)
                    end
                end
            end
        end
    end
    extras, kinds = Any[], Any[]
    for t in shifts                                     # (e^(jt) Ei(j(U - t)))' = θ^j U'/(U - t)
        Ut = U - lconst(T, t, m)
        (iszero(Ut) || !ok_arg(lq(T, Q(j), m) * Ut)) && continue
        push!(extras, dU / Ut)
        push!(kinds, (:Ei, t))
    end
    for (l, lvl) in enumerate(T.levels[1:m])            # (Ei(j(U - a)))' = θ^j θ_l^(-j) (U - a)'/(U - a), θ_l = exp(a)
        lvl.kind === :exp || continue
        W = U - liftto(T, lvl.arg, m)
        (is_constant(T, W) || !ok_arg(lq(T, Q(j), m) * W)) && continue
        push!(extras, liftto(T, theta(T, l), m)^(-j) * D(T, m, W) / W)
        push!(kinds, (:Eigen, W))
    end
    if m == 0 && isone(jU.den) && degree(jU.num) == 2
        A = crational(jU.num.c[3])
        B, C0 = jU.num.c[2], jU.num.c[1]
        if A !== nothing && (!cx || (cconj_g(T.consts, B) == B && cconj_g(T.consts, C0) == C0))
            push!(extras, one(jU))
            push!(kinds, (:erf, A))
        end
    end
    isempty(extras) && return nothing
    # y' + j U' y + Σ c_e e = α: the parametric Risch DE in K_m (step 9d). Its solution basis
    # has (y, (c₀, c...)) with y' + jU'y = c₀ α + Σ c e; one with c₀ ≠ 0 gives the answer.
    sols = try
        prde(T, m, lq(T, Q(j), m) * dU, Any[α; extras])
    catch e
        e isa RischNotImplemented ? nothing : rethrow()
    end
    sols === nothing && return nothing
    idx = findfirst(s -> !iszero(s[2][1]), sols)
    idx === nothing && return nothing
    y0, c0 = sols[idx]
    s0 = inv(c0[1])
    y = y0 * lconst(T, s0, m)
    cs = [-(c * s0) for c in c0[2:end]]
    terms = Any[]
    X = frac(xpoly(C))
    for (c, kd, e) in zip(cs, kinds, extras)
        iszero(c) && continue
        d = lconst(T, c, i) * liftto(T, e, i) * θj         # (term)' = c e θ^j
        if kd[1] === :Ei
            t = kd[2]
            push!(terms, SpecialTerm(:Ei, c, jq * t, jU - lconst(T, jq * t, m), Q(0), d))
        elseif kd[1] === :Eigen
            push!(terms, SpecialTerm(:Ei, c, zero(C), lq(T, Q(j), m) * kd[2], Q(0), d))
        else
            A = kd[2]
            Ac = cfromQ(C, A)
            B, C0 = jU.num.c[2], jU.num.c[1]
            h = B / (Ac + Ac)
            E = C0 - B * B / (4 * Ac)
            push!(terms, SpecialTerm(A < 0 ? :erf : :erfi, c, E, X + kconst(h), A, d))
        end
    end
    y, terms
end

# a log level whose residue polynomial has non-constant roots: R/(θ + b), b ∈ C, R = c' u^m u'
function special_log(T::Tower, i::Int, R::UPoly, Dsf::UPoly)
    (degree(Dsf) == 1 && degree(R) <= 0) || return nothing
    l1 = lc(Dsf)
    if !isone(l1)                                       # make Dsf = θ + b monic
        R, Dsf = scale(inv(l1), R), scale(inv(l1), Dsf)
    end
    lv = T.levels[i]
    m0 = i - 1
    b = Dsf.c[1]
    bc = dconst_value(T, b)
    bc === nothing && return nothing
    r0 = isempty(R.c) ? zero(T.Ts[i]) : R.c[1]
    iszero(r0) && return nothing
    u = liftto(T, lv.arg, m0)
    du = D(T, m0, u)
    q = r0 / du
    mq = Q(0)
    if dconst_value(T, q) === nothing                   # q = c' u^m: m = (q'/q)/(u'/u)
        mv = dconst_value(T, D(T, m0, q) * u / (q * du))
        mv === nothing && return nothing
        mi = cinteger(mv)
        mi === nothing && return nothing
        mq = mi
    end
    mint = Int(numerator(mq))
    cv = dconst_value(T, q / u^mint)
    cv === nothing && return nothing
    k = mint + 1
    k == 0 && return nothing
    C = ctype(T)
    kc = cfromQ(C, Q(k))
    w = frac(Dsf)                                       # θ + b at level i
    d = frac(UPoly{T.Ts[i]}(T.Ts[i][r0]), Dsf)          # the integrand R/Dsf
    SpecialTerm(:Ei, cv, -(kc * bc), lconst(T, kc, i) * w, Q(0), d)
end

# the term with a given coefficient term `ct` (real fields); zt converts a tower element
function special_out(b::Builder, q::SpecialTerm, ct, zt)
    if q.fn === :Ei
        core = mk(b, :Ei, zt(q.z))
    else
        sa = mk(b, :sqrt, cterm(b, abs(q.A)))
        core = mk(b, :*, mk(b, :/, mk(b, :sqrt, b.lift(π)), mk(b, :*, b.lift(2), sa)),
                  mk(b, q.fn, mk(b, :*, sa, zt(q.z))))
    end
    parts = Any[]
    isone(q.c) || push!(parts, ct)
    iszero(q.p) || push!(parts, mk(b, :exp, cterm(b, q.p)))
    isempty(parts) ? core : mk(b, :*, parts..., core)
end

# leading rational coefficient of a nested Frac / constant (for a sign)
lead_rational(c::Q) = c
lead_rational(c::QI) = iszero(c.re) ? c.im : c.re
lead_rational(c::QSB) = lead_rational(iszero(c.a) ? c.b : c.a)
lead_rational(c::Frac) = iszero(c) ? Q(0) : lead_rational(lc(c.num))

# Re(c e^p F(z)) over ℚ(i): Ei of a real z, or Ei(i w) ~ Ci(w) + i Si(w) for real w
function special_out_real(b::Builder, T::Tower, kinds, q::SpecialTerm)
    C = ctype(T)
    gens = T.consts
    half = inv(cfromQ(C, Q(2)))
    I = cimag(C)
    rpart(c) = (c + cconj_g(gens, c)) * half
    ipart(c) = (c - cconj_g(gens, c)) * inv(I + I)
    cr, ci, pr, ps = rpart(q.c), ipart(q.c), rpart(q.p), ipart(q.p)
    zt(z) = real_term(b, T, kinds, z)
    if q.fn !== :Ei                                      # erf/erfi: real argument and prefactor
        iszero(ci) && iszero(ps) || throw(RischNotImplemented("erf of a complex argument has no real form here"))
        iszero(cr) && return b.lift(0)
        return special_out(b, SpecialTerm(q.fn, cr, pr, q.z, q.A, q.deriv), cterm(b, cr), zt)
    end
    # κ = c e^p = e^pr (cr + i ci)(cos ps + i sin ps):  κ_r, κ_i as terms (nothing for zero)
    ep = iszero(pr) ? nothing : mk(b, :exp, cterm(b, pr))
    function combo(a1, a2)                               # e^pr (a1 cos ps + a2 sin ps)
        ts = Any[]
        if iszero(ps)
            iszero(a1) || push!(ts, cterm(b, a1))
        else
            iszero(a1) || push!(ts, mk(b, :*, cterm(b, a1), mk(b, :cos, cterm(b, ps))))
            iszero(a2) || push!(ts, mk(b, :*, cterm(b, a2), mk(b, :sin, cterm(b, ps))))
        end
        isempty(ts) && return nothing
        t = length(ts) == 1 ? ts[1] : mk(b, :+, ts...)
        ep === nothing ? t : mk(b, :*, ep, t)
    end
    κr = combo(cr, -ci)
    κi = combo(ci, cr)
    lvl = levelof(T, q.z)
    sz = tconj(T, kinds, q.z, lvl)
    if sz == q.z
        κr === nothing && return b.lift(0)
        return mk(b, :*, κr, mk(b, :Ei, zt(q.z)))
    end
    sz == -q.z || throw(RischNotImplemented("Ei of a complex argument has no real form here"))
    w = q.z * lconst(T, -I, lvl)                        # z = i w, w real
    flip = lead_rational(w) < 0                         # Ci(-w) ~ Ci(w), Si(-w) = -Si(w)
    flip && (w = -w)
    ts = Any[]
    κr === nothing || push!(ts, mk(b, :*, κr, mk(b, :Ci, zt(w))))
    if κi !== nothing                                   # Re(κ (Ci + i Si)) = κr Ci - κi Si
        st = mk(b, :*, κi, mk(b, :Si, zt(w)))
        push!(ts, flip ? st : mk(b, :*, b.lift(-1), st))
    end
    isempty(ts) && return b.lift(0)
    length(ts) == 1 ? ts[1] : mk(b, :+, ts...)
end

# ---------------------------------------------------------------------------
# Step 7: real form of results over ℚ(i)
#
# Complex conjugation σ (i ↦ -i, x real) acts on a tower whose generators are real
# (exp or log of real elements: σθ = θ) or trigonometric (θ = exp(i·w), w real: σθ = 1/θ).
# σ commutes with the derivation, so for a real integrand f and ∫ f = F computed over ℚ(i),
# Re F = (F + σF)/2 is an antiderivative too, and it has a real form:
#   (v + σv)/2                      σ-invariant; on a :trig level written with cos(kw), sin(kw)
#   (c log w + σc log σw)/2   =     c_r/2 log(w σw) - c_i atan(V/U)
#       c_r = (c + σc)/2, c_i = (c - σc)/(2i), U = (w + σw)/2, V = (w - σw)/(2i)
#   (c_r log w when w is real). The real form is re-verified exactly in the tower.
# ---------------------------------------------------------------------------
function sigma_kinds(T::Tower)
    kinds = Symbol[]
    for (i, lv) in enumerate(T.levels)
        sa = tconj(T, kinds, lv.arg, levelof(T, lv.arg))
        if sa == lv.arg
            push!(kinds, :real)
        elseif lv.kind === :exp && sa == -lv.arg
            push!(kinds, :trig)
        else
            throw(RischNotImplemented(
                "generator $i ($(lv.kind)) is neither real nor exp(i·real): no real form"))
        end
    end
    kinds
end

# σ on an element of level i (needs the kinds of levels 1..i)
function tconj(T::Tower, kinds, f, i::Int)
    i == 0 && return frac(cpconj_g(T.consts, f.num), cpconj_g(T.consts, f.den))   # x real
    iszero(f) && return f
    n = tconj_poly(T, kinds, f.num, i)
    d = tconj_poly(T, kinds, f.den, i)
    kinds[i] === :real && return frac(n, d)
    θ = xpoly(T.Ts[i])          # θ ↦ 1/θ: p(θ) ↦ θ^(-deg p) p̃(θ), p̃ = reversed conjugated coefficients
    frac(n * θ^degree(f.den), d * θ^degree(f.num))
end
function tconj_poly(T::Tower, kinds, p::UPoly, i::Int)
    K = T.Ts[i]
    cs = K[tconj(T, kinds, c, i - 1) for c in p.c]
    kinds[i] === :trig && reverse!(cs)
    UPoly{K}(cs)
end

# Laurent polynomials in θ as Dict(k => coefficient)
laurent_of(p::UPoly{K}) where {K} = Dict{Int,K}(k - 1 => c for (k, c) in enumerate(p.c) if !iszero(c))
laurent_conj(T::Tower, kinds, p::UPoly{K}, i::Int) where {K} =        # Σ σ(c_k) θ^(-k)
    Dict{Int,K}(-(k - 1) => tconj(T, kinds, c, i - 1) for (k, c) in enumerate(p.c) if !iszero(c))
function laurent_mul(a::Dict{Int,K}, b::Dict{Int,K}) where {K}
    r = Dict{Int,K}()
    for (i, x) in a, (j, y) in b
        s = get(r, i + j, zero(K)) + x * y
        iszero(s) ? delete!(r, i + j) : (r[i + j] = s)
    end
    r
end

# a σ-invariant element of level i as a real term
function real_term(b::Builder, T::Tower, kinds, f, i::Int = levelof(T, f))
    i == 0 && return frac_term(b, f)            # σ-invariant: real coefficients (cterm checks)
    lv = T.levels[i]
    if kinds[i] === :real
        th = mk(b, lv.kind, real_term(b, T, kinds, lv.arg))
        n = real_poly_term(b, T, kinds, f.num, i, th)
        return isone(f.den) ? n : mk(b, :/, n, real_poly_term(b, T, kinds, f.den, i, th))
    end
    # :trig, θ = exp(i w):  f = N/D = (N·σD)/(D·σD) with σ-invariant Laurent numerator and denominator
    sD = laurent_conj(T, kinds, f.den, i)
    A = laurent_mul(laurent_of(f.num), sD)
    B = laurent_mul(laurent_of(f.den), sD)
    C = ctype(T)
    w = liftto(T, lv.arg, i - 1) * lconst(T, -cimag(C), i - 1)
    wt = real_term(b, T, kinds, w)
    num = real_laurent_term(b, T, kinds, A, i, wt)
    if length(B) == 1 && haskey(B, 0)
        return isone(B[0]) ? num : mk(b, :/, num, real_term(b, T, kinds, B[0], i - 1))
    end
    mk(b, :/, num, real_laurent_term(b, T, kinds, B, i, wt))
end

function real_poly_term(b::Builder, T::Tower, kinds, p::UPoly, i::Int, th)
    iszero(p) && return b.lift(0)
    ts = Any[]
    for (k, c) in enumerate(p.c)
        iszero(c) && continue
        e = k - 1
        if e == 0
            push!(ts, real_term(b, T, kinds, c, i - 1))
        else
            thk = e == 1 ? th : mk(b, :^, th, b.lift(e))
            push!(ts, isone(c) ? thk : mk(b, :*, real_term(b, T, kinds, c, i - 1), thk))
        end
    end
    length(ts) == 1 ? ts[1] : mk(b, :+, ts...)
end

# Σ a_k θ^k with a_(-k) = σ(a_k):  a_0 + Σ_(k>0) (a_k + a_(-k)) cos(kw) + i(a_k - a_(-k)) sin(kw)
function real_laurent_term(b::Builder, T::Tower, kinds, L::Dict, i::Int, wt)
    K = T.Ts[i]
    all(k -> haskey(L, -k), keys(L)) || throw(RischError("real form: Laurent polynomial is not σ-invariant"))
    I = lconst(T, cimag(ctype(T)), i - 1)
    ts = Any[]
    c0 = get(L, 0, zero(K))
    iszero(c0) || push!(ts, real_term(b, T, kinds, c0, i - 1))
    for k in sort([k for k in keys(L) if k > 0])
        ck, cm = L[k], L[-k]
        kw = k == 1 ? wt : mk(b, :*, b.lift(k), wt)
        for (coef, fn) in ((ck + cm, :cos), (I * (ck - cm), :sin))
            iszero(coef) && continue
            tr = mk(b, fn, kw)
            push!(ts, isone(coef) ? tr : mk(b, :*, real_term(b, T, kinds, coef, i - 1), tr))
        end
    end
    isempty(ts) && return b.lift(0)
    length(ts) == 1 ? ts[1] : mk(b, :+, ts...)
end

# --- continuous arguments (step TC) ----------------------------------------------
# Re(c log w) = Re c·log|w| - Im c·arg w. The piece atan(V/U) for arg w jumps where U = 0. When
# w = Σ c_k z^k has constant coefficients (c_k ∈ C = ℚ(i) or ℚ(i)(√d)) and z is a real variable
# (x at the base, θ at a real exp/log level), w = A(z) + i B(z) with A, B real polynomials and
# Rioboo's LogToAtan gives arg w ≡ -Σ atan(pⱼ(z)), continuous. At a trig level θ = e^{iu}, with
# t = tan(u/2) (θ = (1 + it)/(1 - it)):  w(θ) = (1 - it)^(-n) w̃(t), w̃(t) = Σ c_k (1+it)^k (1-it)^(n-k),
# so arg w = n·u/2 + arg w̃(t) on (-π, π), and arg w̃ ≡ -Σ atan(pⱼ(t)). At u = π mod 2π (t = ±∞) each
# odd pⱼ jumps by -sign(lc pⱼ)·π, together mπ; the correction -mπ⌊(u+π)/2π⌋ is -(m/2)(u - 2 atan t):
#   arg w ≡ ((n - m)/2)·u - Σ atan(pⱼ(t)) + m·atan(t)          (continuous for all real u)
# t = -i(θ - 1)/(θ + 1) is a tower element, so every piece is still differentiated and checked
# exactly in `to_term_real`. Pieces: (factor, :atan | :lin, element, printer b -> term).
real_field(::Type{QI}) = Q
real_field(::Type{QSB{d,QI}}) where {d} = QS{d}
real_field(::Type) = nothing
re_part(c::QI) = c.re
im_part(c::QI) = c.im
re_part(c::QSB{d,QI}) where {d} = QS{d}(c.a.re, c.b.re)
im_part(c::QSB{d,QI}) where {d} = QS{d}(c.a.im, c.b.im)
to_complex(::Type{QI}, r::Q) = QI(r, Q(0))
to_complex(::Type{QSB{d,QI}}, r::QS{d}) where {d} = QSB{d,QI}(QI(r.a, Q(0)), QI(r.b, Q(0)))
real_sign(r::Q) = sign(r)
function real_sign(r::QS{d}) where {d}                  # sign of a + b√d, d > 0
    a, b = r.a, r.b
    (sign(a) == sign(b) || iszero(b)) && return sign(a) + (iszero(a) ? sign(b) : 0)
    a^2 > d * b^2 ? sign(a) : sign(b)
end

# p(z) for p over the real field, z a term (printing)
function rpoly_term(b::Builder, p::UPoly, zt)
    ts = Any[]
    for (k, c) in enumerate(p.c)
        iszero(c) && continue
        e = k - 1
        zk = e == 0 ? nothing : (e == 1 ? zt : mk(b, :^, zt, b.lift(e)))
        push!(ts, zk === nothing ? cterm(b, c) : (isone(c) ? zk : mk(b, :*, cterm(b, c), zk)))
    end
    isempty(ts) ? b.lift(0) : (length(ts) == 1 ? ts[1] : mk(b, :+, ts...))
end

# number of times the tan(u/2) form of TC was used (read by `bioche`, step TB)
const HALF_ANGLE_FORMS = Ref(0)

function continuous_arg_pieces(T::Tower, kinds, j::Int, w)
    C = ctype(T)
    RT = real_field(C)
    RT === nothing && return nothing
    isone(w.den) || return nothing
    cs = C[]
    for c in w.num.c
        v = j == 0 ? c : const_value(T, c)
        v === nothing && return nothing
        push!(cs, v)
    end
    n = length(cs) - 1
    n >= 1 || return nothing
    I = cimag(C)
    P = UPoly{C}
    trig = j > 0 && kinds[j] === :trig
    if trig
        ap, am = P(C[one(C), I]), P(C[one(C), -I])
        wt = sum(scale(cs[k + 1], ap^k * am^(n - k)) for k in 0:n)
        θ = frac(xpoly(T.Ts[j]))
        zel = lconst(T, -I, j) * (θ - one(θ)) / (θ + one(θ))           # t = tan(u/2)
        uel = liftto(T, T.levels[j].arg, j - 1) * lconst(T, -I, j - 1)  # θ = e^{iu}
        uterm = b -> real_term(b, T, kinds, uel)
        zterm = b -> mk(b, :tan, mk(b, :/, uterm(b), b.lift(2)))
    else
        wt = P(cs)
        if j == 0
            zel = frac(xpoly(C))
            zterm = b -> b.x
        else
            lv = T.levels[j]
            zel = frac(xpoly(T.Ts[j]))
            zterm = b -> mk(b, lv.kind, real_term(b, T, kinds, lv.arg))
        end
    end
    A = UPoly{RT}(RT[re_part(c) for c in wt.c])
    B = UPoly{RT}(RT[im_part(c) for c in wt.c])
    (iszero(A) || iszero(B)) && return nothing
    peval_el(p) = foldr((c, acc) -> acc * zel + lconst(T, to_complex(C, c), j), p.c; init = zero(zel))
    out = Any[]
    m = 0
    for p in log_to_atan(A, B)                          # Σ 2 atan(p) ≡ 2 atan(A/B) ≡ -2 arg w̃
        degree(p) <= 0 && continue                      # a constant: derivative 0
        push!(out, (-one(C), :atan, peval_el(p), b -> rpoly_term(b, p, zterm(b))))
        trig && isodd(degree(p)) && (m += Int(real_sign(lc(p))))
    end
    if trig && iseven(n - m)                            # the shortcut without tan(u/2) (step TH)
        sh = shifted_arg_pieces(T, kinds, j, w, (n - m) ÷ 2, uel, uterm)
        sh === nothing || return sh
    end
    trig && (HALF_ANGLE_FORMS[] += 1)                   # the tan(u/2) form is used (see `bioche`)
    if trig
        n != m && push!(out, (cfromQ(C, Q(n - m) // 2), :lin, uel, uterm))
        m != 0 && push!(out, (cfromQ(C, Q(m)), :atan, zel, zterm))
    end
    out
end

# Step TH. At a trig level, w of winding number s around the unit circle (s = (n - m)/2 above):
# arg w = s·u + arg v, v = θ^(-s) w, and v = A + iB with A = (v + σv)/2, B = (v - σv)/(2i) real
# trigonometric polynomials. If A never vanishes on the real line, arg v ≡ atan(B/A) (continuous);
# if B never does, arg v ≡ -atan(A/B). "Never vanishes" is decided exactly: with t = tan(u/2),
# A·(1 + t²)^K = Σ a_k (1+it)^(K+k) (1-it)^(K-k) is a real polynomial without real roots (Sturm), and
# A(π) = Σ a_k (-1)^k ≠ 0. Returns the pieces of arg w, or nothing (then the tan(u/2) form is used).
function shifted_arg_pieces(T::Tower, kinds, j::Int, w, s::Int, uel, uterm)
    C = ctype(T)
    RT = real_field(C)
    I = cimag(C)
    θel = frac(xpoly(T.Ts[j]))
    v = s >= 0 ? w / θel^s : w * θel^(-s)
    sv = tconj(T, kinds, v, j)
    half = lconst(T, inv(cfromQ(C, Q(2))), j)
    Av, Bv = (v + sv) * half, (v - sv) * lconst(T, inv(I + I), j)
    (iszero(Av) || iszero(Bv)) && return nothing
    # Laurent coefficients a_k (k = -K … ) of a σ-invariant X = N/θ^K, as real constants
    function nonvanishing(X)
        degree(X.den) == length(X.den.c) - 1 && all(iszero, X.den.c[1:(end - 1)]) || return false
        K = degree(X.den)
        a = [const_value(T, c) for c in X.num.c]
        any(isnothing, a) && return false
        P = UPoly{C}
        ap, am = P(C[one(C), I]), P(C[one(C), -I])
        Ah = sum(scale(a[l + 1], ap^l * am^(2K - l)) for l in eachindex(a) .- 1)
        all(c -> iszero(im_part(c)), Ah.c) || return false
        Ar = UPoly{RT}(RT[re_part(c) for c in Ah.c])
        Aπ = sum(re_part(a[l + 1]) * (iseven(l - K) ? 1 : -1) for l in eachindex(a) .- 1)
        !iszero(Aπ) && real_root_count(Ar, nothing, nothing, c -> Int(real_sign(c))) == 0
    end
    out = Any[]
    s != 0 && push!(out, (cfromQ(C, Q(s)), :lin, uel, uterm))
    # printed as real_term(B)/real_term(A): each is σ-invariant (no conjugate denominator to multiply in)
    ratio(X, Y) = b -> mk(b, :/, real_term(b, T, kinds, X, j), real_term(b, T, kinds, Y, j))
    if nonvanishing(Av)
        push!(out, (one(C), :atan, Bv / Av, ratio(Bv, Av)))
    elseif nonvanishing(Bv)
        push!(out, (-one(C), :atan, Av / Bv, ratio(Av, Bv)))
    else
        return nothing
    end
    out
end

# Re(c log w) as real pieces (coefficient, :log | :atan | :lin, argument[, printer]), see above
function real_log_pieces(T::Tower, kinds, c, w)
    C = ctype(T)
    j = levelof(T, w)
    sw = tconj(T, kinds, w, j)
    sc = cconj_g(T.consts, c)
    half = inv(cfromQ(C, Q(2)))
    I = cimag(C)
    cr = (c + sc) * half
    ci = (c - sc) * inv(I + I)
    pieces = Any[]
    if sw == w
        iszero(cr) || push!(pieces, (cr, :log, w))
        return pieces
    end
    iszero(cr) || push!(pieces, (cr * half, :log, w * sw))
    U = (w + sw) * lconst(T, half, j)
    V = (w - sw) * lconst(T, inv(I + I), j)
    if !(iszero(ci) || iszero(U) || iszero(V))
        cp = continuous_arg_pieces(T, kinds, j, w)      # -Im c · arg w, continuous (step TC)
        if cp !== nothing
            for pc in cp                                # (factor, kind, argument[, printer])
                push!(pieces, (-ci * pc[1], pc[2:end]...))
            end
            return pieces
        end
    end
    if !(iszero(ci) || iszero(U) || iszero(V))          # U = 0: w/σw = -1, constant
        a = V / U
        # at the base, atan(V/U) with V constant has a pole where U = 0; -atan(U/V) has the same
        # derivative and is continuous there (e.g. atan(1/t) -> -atan(t))
        if j == 0 && degree(a.num) <= 0 && degree(a.den) > 0
            push!(pieces, (ci, :atan, inv(a)))
        else
            push!(pieces, (-ci, :atan, a))
        end
    end
    pieces
end

# combine real pieces with the same argument (atan(-u) = -atan(u)); zero coefficients dropped
function merge_pieces(pieces)
    out = Any[]
    for pc in pieces
        c, k, a = pc[1], pc[2], pc[3]
        i = findfirst(p -> p[2] === k && p[3] == a, out)
        if i !== nothing
            out[i] = (out[i][1] + c, out[i][2:end]...)
            continue
        end
        i = k === :atan ? findfirst(p -> p[2] === :atan && p[3] == -a, out) : nothing
        if i !== nothing
            out[i] = (out[i][1] - c, out[i][2:end]...)
            continue
        end
        push!(out, pc)
    end
    filter(p -> !iszero(p[1]), out)
end

# the real form of an integral over ℚ(i) as a term, verified: D(real form) == f in T
function to_term_real(b::Builder, T::Tower, L::Int, res::ElemIntegral, f)
    kinds = sigma_kinds(T)
    C = ctype(T)
    v = liftto(T, res.v, L)
    vr = (v + tconj(T, kinds, v, L)) * lconst(T, inv(cfromQ(C, Q(2))), L)
    tot = D(T, L, vr)
    ts = Any[]
    iszero(vr) || push!(ts, real_term(b, T, kinds, vr, L))
    function emit!(TT, kk, pieces)              # push the terms, return Σ derivatives (in TT)
        ds = zero(TT.Ts[L + 1])
        for pc in pieces
            coef, kind, arg = pc[1], pc[2], pc[3]
            a = liftto(TT, arg, L)
            da = kind === :log ? D(TT, L, a) / a : kind === :lin ? D(TT, L, a) : D(TT, L, a) / (one(a) + a * a)
            ds = ds + lconst(TT, coef, L) * da
            at = length(pc) >= 4 ? pc[4](b) : real_term(b, TT, kk, arg)
            t = kind === :lin ? at : mk(b, kind, at)
            push!(ts, isone(coef) ? t : mk(b, :*, cterm(b, coef), t))
        end
        ds
    end
    pieces = Any[]
    for (c, w) in res.logs
        append!(pieces, real_log_pieces(T, kinds, c, w))
    end
    tot = tot + emit!(T, kinds, merge_pieces(pieces))
    isempty(res.atans) || throw(RischError("unexpected atan terms over ℚ(i)"))
    for q in res.quads
        q isa SpecialTerm || continue
        d = liftto(T, q.deriv, L)                       # Re of the term differentiates to (d + σd)/2
        tot = tot + (d + tconj(T, kinds, d, L)) * lconst(T, inv(cfromQ(C, Q(2))), L)
        push!(ts, special_out_real(b, T, kinds, q))
    end
    for q in res.quads
        q isa SpecialTerm && continue
        q isa ExtQuadPair || throw(RischError("unexpected term $(typeof(q)) over ℚ(i)"))
        T2 = q.T2
        k2 = sigma_kinds(T2)
        a2, W2 = galois_d(q.a), change_constants(T2, T2, q.W, galois_d)
        ds = emit!(T2, k2, merge_pieces(vcat(real_log_pieces(T2, k2, q.a, q.W),
                                             real_log_pieces(T2, k2, a2, W2))))
        tot = tot + change_constants(T2, T, ds, qs_down)
    end
    tot == liftto(T, f, L) ||
        throw(RischError("internal check failed: the real form of the antiderivative does not differentiate back"))
    isempty(ts) && return b.lift(0)
    length(ts) == 1 ? ts[1] : mk(b, :+, ts...)
end

# ---------------------------------------------------------------------------
# Step 10a: radicals of one linear-fractional radicand, by substitution
#
# All radicals u^(p/q) (sqrt, cbrt, ^ with a non-integer rational exponent) must share one
# radicand u = (a x + b)/(c x + d) ∈ ℚ(x) with ad - bc ≠ 0. With n = lcm of the q's and
# t = u^(1/n):  x = φ(t) = (b - d tⁿ)/(c tⁿ - a),  u^(p/q) = t^(pn/q),  dx = φ'(t) dt.
# The integrand is parsed straight into a tower over ℚ(t) (parse hook `T.subst`), multiplied
# by φ'(t), integrated and verified exactly there; the answer is printed with the base
# variable t written as the term u^(1/n) (sqrt(u) for n = 2), i.e. as a function of x.
# Anything else with radicals (several radicands, radicands of degree ≥ 2, nested radicals)
# raises RischNotImplemented. Principal roots: answers are valid where u > 0.
# ---------------------------------------------------------------------------

# (exponent, radicand term) when t is u^e with e ∈ ℚ \ ℤ (sqrt, cbrt, ^), else nothing
function radical_parts(t)
    safe_iscall(t) || return nothing
    args = arguments(t)
    isempty(args) && return nothing
    n = opname(operation(t))
    n === :sqrt && length(args) == 1 && return (Q(1) // 2, args[1])
    n === :cbrt && length(args) == 1 && return (Q(1) // 3, args[1])
    if n === :^ && length(args) == 2 && !is_e_const(args[1])
        e = leaf_rational(args[2])
        (e !== nothing && !isone(denominator(e))) && return (Q(e), args[1])
    end
    nothing
end

# all radicals of f: [(exponent, radicand term)]
function collect_radicals(f, xk::String, out = Tuple{Q,Any}[])
    rp = radical_parts(f)
    rp === nothing || push!(out, rp)
    if safe_iscall(f)
        for a in arguments(f)
            collect_radicals(a, xk, out)
        end
    end
    out
end

# the radicand as an element of ℚ(x), or nothing
function radicand_element(u, xk::String)
    T, el = try
        build_tower(u, xk)
    catch e
        (e isa RischNotImplemented || e isa RischError) && return nothing
        rethrow()
    end
    (isempty(T.levels) && ctype(T) === Q) ? el : nothing
end

# φ ∈ S(t) (same representation as S(x); S = ℚ or the tower's constant field) as an element
# of K_0 of the tower T
to_K0(T::Tower, φ::Frac{UPoly{Q}}) = (C = ctype(T); P = UPoly{C};
    frac(P(C[cfromQ(C, c) for c in φ.num.c]), P(C[cfromQ(C, c) for c in φ.den.c])))
to_K0(T::Tower{C}, φ::Frac{UPoly{C}}) where {C} = φ

function integrate_radical(f, x, rads; build = nothing, lift = nothing, verify::Bool = true)
    xk = string(x)
    groups = Any[]                                      # [radicand element, term, lcm of indices]
    cvs = Q[]                                           # radicands of constant radicals (10e)
    for (e, ut) in rads
        ue = radicand_element(ut, xk)
        ue === nothing && throw(RischNotImplemented(
            "radical of a non-rational expression ($ut): only radicals of rational functions of x are supported"))
        if is_const_radicand(ue)
            denominator(e) == 2 || throw(RischNotImplemented(
                "the constant radical $ut: only square roots of rational constants are supported"))
            push!(cvs, const_radicand(ue))
            continue
        end
        i = findfirst(g -> g[1] == ue, groups)
        i === nothing && (push!(groups, Any[ue, ut, 1]); i = length(groups))
        groups[i][3] = lcm(groups[i][3], Int(denominator(e)))
    end
    b0 = Builder(build === nothing ? auto_build(f, x) : build,
                 lift === nothing ? auto_lift(f, x) : lift, x)
    cfix = const_radical_field(cvs)
    if isempty(groups)                                  # only constant radicals: x = t
        tt = frac(xpoly(Q))
        return try_substitutions(f, xk, Any[(Q, tt, (ue, e) -> throw(RischError("unexpected radicand")), x)],
                                 b0, verify, cfix)
    end
    length(groups) == 2 && return integrate_two_radicals(f, xk, groups, b0, verify, cfix)
    length(groups) > 2 && throw(RischNotImplemented(
        "radicals of more than two different radicands (a curve of genus ≥ 1 in general)"))
    u, uterm, n = groups[1]
    N, Dd = u.num, u.den
    co(p, i) = i <= length(p.c) ? p.c[i] : Q(0)
    P = UPoly{Q}
    tt = frac(xpoly(Q))                                 # t ∈ ℚ(t)
    kq(c) = frac(P(Q[c]))
    if degree(N) <= 1 && degree(Dd) <= 1 && degree(N) + degree(Dd) >= 1
        # 10a: u = (a x + b)/(c x + d), t = u^(1/n), x = (b - d tⁿ)/(c tⁿ - a), u^(p/q) = t^(pn/q)
        a, b, c, d = co(N, 2), co(N, 1), co(Dd, 2), co(Dd, 1)
        iszero(a * d - b * c) && throw(RischError("radicand is constant"))
        tn = tt^n
        φ = (kq(b) - kq(d) * tn) / (kq(c) * tn - kq(a))
        tterm = n == 2 ? mk(b0, :sqrt, uterm) : mk(b0, :^, uterm, b0.lift(Q(1) // n))
        cands = Any[(Q, φ, k -> tt^k, tterm)]          # u^(k/n) = t^k
    elseif isone(Dd) && degree(N) == 2 && n == 2
        # 10b/10c: √Q, Q = A x² + B x + C, by an Euler substitution (rational parametrisation
        # over ℚ, or over ℚ(i)(√d) when the conic R² = Q has no small rational point);
        # Q^(k/2) = ψ(t)^k
        cands = Any[(S, φ, k -> ψ^k, tterm)
                    for (S, φ, ψ, tterm) in euler_substitution(co(N, 3), co(N, 2), co(N, 1), b0, uterm; pref = cfix_d(cfix))]
    else
        throw(RischNotImplemented(
            "radicals of $uterm: supported are u^(p/q) with u = (ax+b)/(cx+d), and √ of a quadratic " *
            "polynomial; this needs the algebraic Risch algorithm or is not elementary in general"))
    end
    radval(radpow) = function (ue, e)                   # u^e = radpow(e n)
        ue == u || throw(RischError("unexpected radicand"))
        k = e * n
        isone(denominator(k)) || throw(RischError("radical exponent not a multiple of 1/n"))
        radpow(Int(numerator(k)))
    end
    try_substitutions(f, xk, Any[(S, φ, radval(radpow), tterm) for (S, φ, radpow, tterm) in cands], b0, verify, cfix)
end

# Several substitutions (different constant fields, 10c/10d): the first one that is handled
# decides; a NotElementary from any of them is a proof (each is a rational parametrisation).
# With constant radicals (10e, `cfix` = (field, value function)) the tower is built over
# cfix.C; a substitution over another field ℚ(i)(√d') is not combinable (skipped).
function try_substitutions(f, xk::String, cands, b0::Builder, verify::Bool, cfix = nothing)
    err = RischNotImplemented("the radicals of x need a constant field other than the one fixed by the constant radicals ($(cfix === nothing ? Q : cfix.C))")
    for (S, φ, radval, tterm) in cands
        C = cfix === nothing || cfix.C === Q ? (S === Q ? nothing : S) :
            (S === Q || S === cfix.C) ? cfix.C : continue
        try
            return integrate_subst(f, xk, S, φ, radval, Builder(b0.build, b0.lift, tterm), verify, C, cfix)
        catch e
            e isa RischNotImplemented || rethrow()
            err = e
        end
    end
    throw(err)
end

# ∫ f dx with x = φ(t) and u^e = radval(u, e) ∈ S(t) for the radicands u ∈ ℚ(x);
# the answer is printed with t as bt.x
function integrate_subst(f, xk::String, ::Type{S}, φ, radval, bt::Builder, verify::Bool,
                         constants = S === Q ? nothing : S, cfix = nothing) where {S}
    dφ = dx(φ)
    function sub(term, T)
        if !safe_iscall(term)
            return string(term) == xk ? to_K0(T, φ) : nothing
        end
        rp = radical_parts(term)
        rp === nothing && return nothing
        e, ut = rp
        ue = radicand_element(ut, xk)
        ue === nothing && throw(RischNotImplemented("radical of a non-rational expression ($ut)"))
        if is_const_radicand(ue)
            C = ctype(T)
            c = cfix.val(const_radicand(ue), e)
            return frac(UPoly{C}(C[c isa Q ? cfromQ(C, c) : c]))
        end
        to_K0(T, radval(ue, e))
    end
    T, el = build_tower(f, xk; subst = sub, constants = constants)
    T.subst = nothing
    g = el * liftto(T, to_K0(T, dφ), levelof(T, el))     # f(φ(t), …) φ'(t)
    T, g = minimal(T, g)
    bd = Builder(bt.build, bt.lift, bt.x, T.consts)
    integrate_built(T, g, bd, verify)
end

# ---------------------------------------------------------------------------
# Step 10e: square roots of rational constants (sqrt(2), 2^(3/2), sqrt(8), …) as constants
#
# All must lie in one field ℚ(√d) (d the squarefree part of the radicands, d > 0); the tower
# is then built over ℚ(i)(√d) (as in 10c: i for the atan terms, real-form output, sqrt(d)
# symbolic). v^(p/2) = v^((p-1)/2) √v, √v = σ√d. Radicals of x combine with it when their
# substitution is over ℚ or over the same field.
# ---------------------------------------------------------------------------
is_const_radicand(u) = degree(u.num) <= 0 && degree(u.den) <= 0
cfix_d(cfix) = cfix === nothing || cfix.C === Q ? 1 : cfix.C.parameters[1]   # d of ℚ(i)(√d)
const_radicand(u) = isempty(u.num.c) ? Q(0) : u.num.c[1] / u.den.c[1]

# (C, val) with val(v, e) = v^e ∈ C for the constant radicands vs, or nothing if there are none
function const_radical_field(vs)
    isempty(vs) && return nothing
    any(v -> v < 0, vs) && throw(RischNotImplemented(
        "square roots of negative constants (complex constants in the integrand) are not supported"))
    ds = unique([sqfree_split(numerator(v) * denominator(v))[2] for v in vs if !iszero(v)])
    filter!(!isone, ds)
    length(ds) > 1 && throw(RischNotImplemented(
        "square roots of constants with different squarefree parts $(Int.(ds)) (would need ℚ(√d₁, √d₂))"))
    C = isempty(ds) ? Q : QSB{Int(ds[1]),QI}
    function val(v::Q, e::Q)
        iszero(v) && return C === Q ? Q(0) : zero(C)
        p = numerator(2 * e)                            # odd: e = p/2
        r = v^((p - 1) ÷ 2)
        sv = rat_sqrt(v)
        sv !== nothing && return r * sv
        _, s = qs_field(v)
        cfromQ(C, r) * s
    end
    (C = C, val = val)
end

# ---------------------------------------------------------------------------
# Step 10d: two radicands, square roots of linear polynomials u₁ = a x + b, u₂ = c x + d
#
# y = √u₁ gives x = (y² - b)/a and u₂ = (c/a) y² + d - c b/a, a quadratic in y without a
# linear term, so √u₂ = R is the 10b/10c case in the variable y: y = φ₂(t), R = ψ₂(t) over S.
# Then x = (φ₂(t)² - b)/a, u₁^(k/2) = φ₂(t)^k, u₂^(k/2) = ψ₂(t)^k (the curve y² = u₁, R² = u₂
# is a conic). Both orders of the radicands are tried. Radicands of higher degree, other
# indices, or three or more radicands give curves of genus ≥ 1 in general: refused.
# ---------------------------------------------------------------------------
function integrate_two_radicals(f, xk::String, groups, b0::Builder, verify::Bool, cfix = nothing)
    linear(u) = isone(u.den) && degree(u.num) == 1
    all(g -> g[3] == 2 && linear(g[1]), groups) || throw(RischNotImplemented(
        "radicals of two different radicands: only square roots of two linear polynomials are supported"))
    cands = Any[]
    for (g1, g2) in (groups, reverse(groups))
        u1, t1, _ = g1
        u2, t2, _ = g2
        b, a = u1.num.c
        d, c = u2.num.c
        by = Builder(b0.build, b0.lift, mk(b0, :sqrt, t1))   # the variable y = √u₁
        eus = try
            euler_substitution(c / a, Q(0), d - c * b / a, by, t2; pref = cfix_d(cfix))
        catch e
            e isa RischNotImplemented || rethrow()
            continue                                    # √u₂ never real where u₁ ≥ 0
        end
        for (S, φ2, ψ2, tterm) in eus
            kS = q -> frac(UPoly{S}(S[cfromQ(S, q)]))
            φ = (φ2 * φ2 - kS(b)) * kS(inv(a))
            radval = function (ue, e)
                k = 2 * e
                isone(denominator(k)) || throw(RischError("radical exponent not a multiple of 1/2"))
                ue == u1 ? φ2^Int(numerator(k)) :
                ue == u2 ? ψ2^Int(numerator(k)) : throw(RischError("unexpected radicand"))
            end
            push!(cands, (S, φ, radval, tterm))
        end
    end
    isempty(cands) && throw(RischNotImplemented(
        "√($(groups[1][2])) and √($(groups[2][2])) are never real at the same point"))
    try_substitutions(f, xk, cands, b0, verify, cfix)
end

# Euler substitutions for R = √(A x² + B x + C): (S, φ, ψ, t-term) with x = φ(t), R = ψ(t),
# φ, ψ ∈ S(t) (identities for the principal root). Over S = ℚ (10b):
#   √A = s ∈ ℚ₊:    R = t - s x,        t = R + s x,        x = (t² - C)/(B + 2 s t)
#   √C = s ∈ ℚ₊:    R = x t + s,        t = (R - s)/x,      x = (2 s t - B)/(A - t²)
#   roots r₁ ≠ r₂:  R = t (x - r₁),     t = R/(x - r₁),     x = (A r₂ - r₁ t²)/(A - t²)
#   (r₁ chosen so that x - r₁ > 0 on the real domain: the smaller root when A < 0)
# Otherwise (10c) through a point (x₀, y₀) of the conic R² = Q(x), y₀ > 0, see `euler_point`:
# a small rational point (S = ℚ), else S = ℚ(i)(√d) with √A (A > 0, the point at infinity) or
# y₀ = √Q(x₀) (x₀ = 0 if C > 0, else the vertex). i is there for the atan terms (residues
# ±i·r); the answer is real (Step 7 real form, sqrt(d) kept symbolic).
function euler_substitution(A::Q, B::Q, C::Q, b::Builder, uterm; pref::Int = 1)
    P = UPoly{Q}
    t = frac(xpoly(Q))
    kq(c) = frac(P(Q[c]))
    R = mk(b, :sqrt, uterm)
    sA = A > 0 ? rat_sqrt(A) : nothing
    if sA !== nothing
        φ = (t * t - kq(C)) / (kq(B) + kq(2 * sA) * t)
        ψ = t - kq(sA) * φ
        tterm = mk(b, :+, R, isone(sA) ? b.x : mk(b, :*, cterm(b, sA), b.x))
        return [(Q, φ, ψ, tterm)]
    end
    sC = C > 0 ? rat_sqrt(C) : nothing
    if sC !== nothing
        φ = (kq(2 * sC) * t - kq(B)) / (kq(A) - t * t)
        ψ = φ * t + kq(sC)
        tterm = mk(b, :/, mk(b, :+, R, cterm(b, -sC)), b.x)
        return [(Q, φ, ψ, tterm)]
    end
    rts = rational_roots(P(Q[C, B, A]))
    if length(rts) == 2
        r1, r2 = A < 0 ? (minimum(rts), maximum(rts)) : (maximum(rts), minimum(rts))
        φ = (kq(A * r2) - kq(r1) * t * t) / (kq(A) - t * t)
        ψ = t * (φ - kq(r1))
        xr = iszero(r1) ? b.x : mk(b, :+, b.x, cterm(b, -r1))
        return [(Q, φ, ψ, mk(b, :/, R, xr))]
    end
    Qv(x0) = (A * x0 + B) * x0 + C
    for h in 1:12, q in 1:h, p in (h - q, q - h)        # small rational points, by height
        gcd(p, q) == 1 || continue
        x0 = Q(p) // Q(q)
        y0 = rat_sqrt(Qv(x0))
        (y0 === nothing || iszero(y0)) && continue
        return [euler_point(Q, y0, A, B, x0, b, uterm)]
    end
    # over ℚ(i)(√d), several candidates (the constants the answer needs are not known in
    # advance, e.g. ∫ dx/(x √(2x² + 3)) needs √3, not √2): √A (A > 0), the point (0, √C)
    # (C > 0), the vertex (A < 0: the maximum of Q, positive if Q ever is)
    cands = Any[]
    if pref > 1                     # 10e: the constant field ℚ(i)(√pref) is fixed: a point with y₀ ∈ ℚ √pref
        for h in 1:12, q in 1:h, p in (h - q, q - h)
            gcd(p, q) == 1 || continue
            x0 = Q(p) // Q(q)
            (Qv(x0) > 0 && rat_sqrt(Qv(x0) / pref) !== nothing) || continue
            push!(cands, euler_point(qs_field(Qv(x0))..., A, B, x0, b, uterm))
            break
        end
    end
    if A > 0                                            # point at infinity: R = t - √A x
        S, s = qs_field(A)
        PS = UPoly{S}
        ts = frac(xpoly(S))
        kS = c -> frac(PS(S[c]))
        φ = (ts * ts - kS(cfromQ(S, C))) / (kS(cfromQ(S, B)) + kS(s + s) * ts)
        ψ = ts - kS(s) * φ
        push!(cands, (S, φ, ψ, mk(b, :+, R, mk(b, :*, cterm(b, s), b.x))))
    end
    for x0 in (Q(0), A < 0 ? -B / (2 * A) : nothing)
        (x0 === nothing || Qv(x0) <= 0) && continue
        any(c -> c[1] === Q, cands) && break
        y0 = rat_sqrt(Qv(x0))
        y0 === nothing ? push!(cands, euler_point(qs_field(Qv(x0))..., A, B, x0, b, uterm)) :
                         push!(cands, euler_point(Q, y0, A, B, x0, b, uterm))
    end
    isempty(cands) && throw(RischNotImplemented("√($uterm): the radicand is never positive: no real square root"))
    unique(c -> c[1], cands)                            # one candidate per constant field
end

# S = ℚ(i)(√d) and √v ∈ S for v ∈ ℚ₊ not a square (v = σ² d, d squarefree)
function qs_field(v::Q)
    σ, d = sqfree_split(numerator(v) * denominator(v))
    S = QSB{Int(d),QI}
    S, S(zero(QI), QI(Q(σ) // Q(denominator(v)), Q(0)))
end

# Euler substitution through the point (x₀, y₀) of R² = Q(x) (y₀ ∈ S, y₀ > 0):
# R = y₀ + t (x - x₀), t = (R - y₀)/(x - x₀); with h = x - x₀, Q(x) = y₀² + Q'(x₀) h + A h²
# gives h = (2 y₀ t - Q'(x₀))/(A - t²), x = x₀ + h, R = y₀ + t h.
function euler_point(::Type{S}, y0::S, A::Q, B::Q, x0::Q, b::Builder, uterm) where {S}
    PS = UPoly{S}
    t = frac(xpoly(S))
    kS(c) = frac(PS(S[c]))
    c(q::Q) = cfromQ(S, q)
    h = (kS(y0 + y0) * t - kS(c(2 * A * x0 + B))) / (kS(c(A)) - t * t)
    φ = kS(c(x0)) + h
    ψ = kS(y0) + t * h
    R = mk(b, :sqrt, uterm)
    xr = iszero(x0) ? b.x : mk(b, :+, b.x, cterm(b, -x0))
    S, φ, ψ, mk(b, :/, mk(b, :+, R, cterm(b, -y0)), xr)
end

# ---------------------------------------------------------------------------
# RootSum: residues that are algebraic of degree > 2 (base level, C = ℚ)
#
# For a residue factor Q(z) (squarefree, no rational roots) left by `log_part` for R/D,
#   Σ_{Q(α)=0} α log W(α, x),   W = gcd(D, R - α D')  in (ℚ[z]/Q)[x], monic in x.
# The gcd is computed by dynamic evaluation (`d5_gcd`): when a leading coefficient is a
# zero divisor mod Q, Q splits (gcd with it) and both parts continue, so Q need not be
# irreducible and no factorisation is needed. Verification is exact in ℚ(x): with the norm
# N = Π_α W(α, x) = res_z(Q, W) and the cofactor N/W (division checked mod Q),
#   d/dx Σ_α α log W(α, x) = Tr_{ℚ[z]/Q}(z · ∂ₓW · N/W) / N,
# the trace through the power sums of the roots of Q (Newton). The result is returned as a
# Risch-owned `RootSum` inside an `IntegralWithRootSums` (the user's packages have no RootSum).
# ---------------------------------------------------------------------------

"""
    RootSum

`Σ_{Q(α)=0} α log W(α, x)`: `poly` is `Q(z)` (monic, squarefree; coefficients low → high) and
`W` the coefficients of `W(z, x)` in `x` (low → high), each a polynomial in `z` reduced mod `Q`.
`var` is how the variable prints and `arg` the term it stands for (after a substitution such as
t = sqrt(1 + x) this is that term; `nothing` when it is the integration variable itself).
Callable: `rs(t)` evaluates the sum numerically at the value `t` of its variable (complex roots,
principal logarithms).
"""
struct RootSum{C}
    poly::UPoly{C}
    W::Vector{UPoly{C}}
    var::String
    arg::Any
end
RootSum{C}(poly, W, var) where {C} = RootSum{C}(poly, W, var, nothing)

"""
    IntegralWithRootSums

An antiderivative `elementary + Σ rootsums` (a term of the user's package plus `RootSum`s, or
`TermRootSum`s for RootSums found inside a tower of exp/log monomials).
`F(a)` evaluates it numerically at a real `a` and returns the real part (the real part of an
antiderivative of a real integrand is an antiderivative too). The logarithms of a RootSum are
continued along the real line from a fixed reference point (not principal values), so `F` is
continuous wherever the integrand is finite and `F(b) - F(a)` is a definite integral.
"""
struct IntegralWithRootSums
    elementary::Any
    rootsums::Vector{Any}            # RootSum (base level) / TermRootSum (inside a tower)
    var::String
end

# coefficients of p (x-poly with coefficients in C[z]) reduced mod m, top zeros dropped
function zmod_trim(m::UPoly{C}, p::Vector{UPoly{C}}) where {C}
    q = UPoly{C}[rem(c, m) for c in p]
    while !isempty(q) && iszero(q[end])
        pop!(q)
    end
    q
end

# p made monic in x modulo m: [(m′, p′)] over a splitting of m (p′ empty: p ≡ 0 mod m′)
function d5_monic(m::UPoly{C}, p::Vector{UPoly{C}}) where {C}
    p = zmod_trim(m, p)
    isempty(p) && return [(m, p)]
    g = monic(gcd(p[end], m))
    if degree(g) == 0
        s, _, g1 = gcdex(p[end], m)                     # s·lc + t·m = g1 ∈ C*
        li = scale_div(s, lc(g1))
        return [(m, zmod_trim(m, UPoly{C}[c * li for c in p]))]
    end
    out = d5_monic(g, p)                                # lc ≡ 0 mod g: the degree drops
    m2 = quo(m, g)
    degree(m2) > 0 && append!(out, d5_monic(m2, p))
    out
end

# a mod b in (C[z]/m)[x], b monic
function d5_rem(m::UPoly{C}, a::Vector{UPoly{C}}, b::Vector{UPoly{C}}) where {C}
    a = copy(a)
    nb = length(b)
    while length(a) >= nb
        c = a[end]
        s = length(a) - nb
        for k in 1:nb
            a[s + k] = a[s + k] - c * b[k]
        end
        a = zmod_trim(m, a)
    end
    a
end

# monic gcd of a and b in (C[z]/m)[x]: [(m′, W)] with m = Π m′
function d5_gcd(m::UPoly{C}, a::Vector{UPoly{C}}, b::Vector{UPoly{C}}) where {C}
    out = Tuple{UPoly{C},Vector{UPoly{C}}}[]
    for (m1, bm) in d5_monic(m, b)
        if isempty(bm)
            append!(out, d5_monic(m1, a))
        else
            append!(out, d5_gcd(m1, bm, d5_rem(m1, a, bm)))
        end
    end
    out
end

# RootSums for an unresolved residue factor (rest, R, D) of `log_part` (D squarefree)
# --- Lazard–Rioboo–Trager (step LR) ------------------------------------------------
# W(α, s) = gcd(D, A - α δD) for the roots α of m, without Euclid in (K[z]/m)[s] (whose coefficients
# swell over function fields such as ℚ(e)). With R(z) = res_s(D, A - z δD) = Π Q_j^j (squarefree),
# a residue of multiplicity j has deg W = j, and W = S_j(α, s), S_j the subresultant of degree j of
# D and A - z δD (Bronstein, IntRationalLogPart), after removing the content of S_j that vanishes
# on Q_j: S_j / Π_k gcd(L_k, Q_j)^k, lc_s(S_j) = Π L_k^k (squarefree). S_j is computed by
# evaluation at z = 0, 1, 2, … (determinants over K) and interpolation: its coefficients have
# degree ≤ deg D - j in z. Then reduced mod m_j = gcd(m, Q_j) and made monic (`d5_monic`). Returns
# [(m′, W)] like `d5_gcd`, or nothing (the caller then uses `d5_gcd`).

# determinant over a field by Bareiss's fraction-free elimination: every division is exact, so
# entries that are polynomials (e.g. in e, when K = ℚ(e)) stay polynomials of bounded size instead
# of becoming growing rational functions as in Gaussian elimination
function field_det(M::Matrix{K}) where {K}
    M = copy(M)
    n = size(M, 1)
    n == 0 && return one(K)
    sgn = 1
    prev = one(K)
    for c in 1:(n - 1)
        if iszero(M[c, c])
            r = findfirst(k -> !iszero(M[k, c]), (c + 1):n)
            r === nothing && return zero(K)
            r += c
            M[c, :], M[r, :] = M[r, :], M[c, :]
            sgn = -sgn
        end
        for k in (c + 1):n, l in (c + 1):n
            M[k, l] = (M[c, c] * M[k, l] - M[k, c] * M[c, l]) / prev
        end
        prev = M[c, c]
    end
    sgn == 1 ? M[n, n] : -M[n, n]
end

# coefficients (s^0 … s^j) of the subresultant of degree j of P (degree m) and Q (degree n), j < m
function subresultant_coeffs(P::UPoly{K}, Q::UPoly{K}, j::Int) where {K}
    m, n = degree(P), degree(Q)
    N = m + n - j                                       # powers s^0 … s^(N-1)
    rows = Vector{K}[]
    for k in 0:(n - j - 1)
        r = fill(zero(K), N)
        for (l, c) in enumerate(P.c)
            r[k + l] = c
        end
        push!(rows, r)
    end
    for k in 0:(m - j - 1)
        r = fill(zero(K), N)
        for (l, c) in enumerate(Q.c)
            r[k + l] = c
        end
        push!(rows, r)
    end
    hi = collect((N - 1):-1:(j + 1))                    # power indices of the fixed columns
    out = K[]
    for i in 0:j
        cols = vcat(hi, i)
        push!(out, isempty(rows) ? zero(K) : field_det(K[rows[r][c + 1] for r in eachindex(rows), c in cols]))
    end
    out
end

function lrt_logs(m::UPoly{K}, D::UPoly{K}, A::UPoly{K}, dD::UPoly{K}) where {K}
    P = UPoly{K}
    mdeg = degree(D)
    n = max(length(A.c), length(dD.c))
    ai(k) = k <= length(A.c) ? A.c[k] : zero(K)
    di(k) = k <= length(dD.c) ? dD.c[k] : zero(K)
    Bat(z) = P(K[ai(k) - z * di(k) for k in 1:n])
    Rz = residue_resultant(D, A, dD)
    out = Tuple{P,Vector{P}}[]
    covered = one(P)
    for (Qj, j) in squarefree(Rz)
        mj = gcd(monic(m), Qj)
        degree(mj) > 0 || continue
        covered = covered * mj
        if j == mdeg
            S = P[P(K[c]) for c in D.c]
        elseif j > mdeg
            return nothing
        else
            zs, vals = K[], Vector{K}[]
            t = 0
            while length(zs) <= mdeg - j
                z = t * one(K)
                t += 1
                B = Bat(z)
                length(B.c) == n || continue
                push!(zs, z)
                push!(vals, subresultant_coeffs(D, B, j))
            end
            S = P[interpolate(zs, K[v[i] for v in vals]) for i in 1:(j + 1)]
            for (L, k) in squarefree(S[end])            # content vanishing on Q_j
                g = gcd(L, Qj)
                degree(g) > 0 || continue
                gk = g^k
                for l in eachindex(S)
                    q, r = divrem(S[l], gk)
                    iszero(r) || return nothing
                    S[l] = q
                end
            end
        end
        for (m2, W) in d5_monic(mj, S)
            length(W) == j + 1 || return nothing
            push!(out, (m2, W))
        end
    end
    degree(covered) == degree(m) ? out : nothing
end

function root_sums(rest::UPoly{C}, R::UPoly{C}, D::UPoly{C}, var::String; arg = nothing) where {C}
    P = UPoly{C}
    dD = deriv(D)
    n = max(length(R.c), length(dD.c))
    ri(i) = i <= length(R.c) ? R.c[i] : zero(C)
    di(i) = i <= length(dD.c) ? dD.c[i] : zero(C)
    a = P[P(C[c]) for c in D.c]
    b = P[P(C[ri(i), -di(i)]) for i in 1:n]             # R - z D'
    out = RootSum{C}[]
    lr = lrt_logs(monic(rest), D, R, dD)
    for (m, W) in (lr === nothing ? d5_gcd(monic(rest), a, b) : lr)
        length(W) >= 2 || throw(RischError("RootSum: trivial gcd for a residue factor"))
        push!(out, RootSum{C}(m, W, var, arg))
    end
    out
end

# power sums p_k = Σ α^k (k = 0 … n-1) of the roots of the monic m (Newton's identities)
function power_sums(m::UPoly{C}) where {C}
    n = degree(m)
    e(i) = m.c[n + 1 - i]                               # coefficient of z^(n-i): (-1)^i e_i
    p = C[cfromQ(C, Q(n))]
    for k in 1:(n - 1)
        s = cfromQ(C, Q(k)) * e(k)
        for i in 1:(k - 1)
            s = s + e(i) * p[k - i + 1]
        end
        push!(p, -s)
    end
    p
end
ztrace(ps, g::UPoly{C}) where {C} = isempty(g.c) ? zero(C) : sum(g.c[k] * ps[k] for k in eachindex(g.c))

# exact d/dx of the RootSum in C(x)
function rootsum_derivative(rs::RootSum{C}) where {C}
    m, W = rs.poly, rs.W
    P = UPoly{C}
    K = Frac{P}
    xp = xpoly(C)
    nz = degree(m)
    Wz = UPoly{K}(K[frac(sum(scale(j <= length(W[k].c) ? W[k].c[j] : zero(C), xp^(k - 1)) for k in eachindex(W)))
                    for j in 1:nz])
    Nr = resultant(UPoly{K}(K[kconst(c) for c in m.c]), Wz)       # Π_α W(α, x), m monic
    isone(Nr.den) || throw(RischError("RootSum: the norm is not a polynomial"))
    N = Nr.num
    Nv = P[P(C[c]) for c in N.c]
    rest = copy(Nv)                                                # N = W · cof mod m
    cof = [zero(P) for _ in 1:(length(Nv) - length(W) + 1)]
    while length(rest) >= length(W)
        c = rest[end]
        s = length(rest) - length(W)
        cof[s + 1] = c
        for k in eachindex(W)
            rest[s + k] = rest[s + k] - c * W[k]
        end
        rest = zmod_trim(m, rest)
    end
    isempty(rest) || throw(RischError("RootSum: W(α, x) does not divide its norm"))
    dW = P[scale(cfromQ(C, Q(k - 1)), W[k]) for k in 2:length(W)]
    zP = P(C[zero(C), one(C)])
    ps = power_sums(m)
    num = zero(P)
    for (i, u) in enumerate(dW), (j, v) in enumerate(cof)
        num = num + scale(ztrace(ps, rem(zP * u * v, m)), xp^(i + j - 2))
    end
    frac(num, N)
end

# --- real form of a quartic RootSum at a tower level (step RF) ----------------------
# As `quartic_real!`, at level i (θ = θᵢ): residues u ± iv, u′ ± iv′ with u, v ∈ ℚ(√d), d > 0
# (`conj_pair_factors`). W = gcd(D, A - (u + iv) δD) is computed over the tower T3 with constants
# ℚ(i)(√d), split as U = (W + W̄)/2, V = (W - W̄)/(2i) (conjugation i ↦ -i is a field automorphism
# commuting with the derivation, so U, V are fixed by it and read back exactly into T2, the tower
# over ℚ(√d)), and each pair gives u log(U² + V²) + v LogToAtan(U, V) (atans of polynomials in θ).
# The exact derivative is computed in T2 and must lie in T (both pairs together are invariant under
# √d ↦ -√d). `corr` is Σ u·deg_θ(U² + V²), the exp correction.
struct TowerRealForm
    T2::Any
    logs::Vector{Any}        # (c ∈ ℚ(√d), w ∈ T2 at level i)
    atans::Vector{Any}       # (c ∈ ℚ(√d), p ∈ T2 at level i, a polynomial in θ)
    corr::Q
    deriv::Any               # ∈ Kᵢ of T
end

function tower_quartic_real(T::Tower, i::Int, A::UPoly, Dn::UPoly, dD::UPoly, q::UPoly{Q})
    for (d, q1) in conj_pair_factors(monic(q))
        S = QS{d}
        B3 = QSB{d,QI}
        pairs = Tuple{S,S}[]
        for qk in (q1, quo(toQS(S, monic(q)), q1))
            u = -qk.c[2] / cfromQ(S, Q(2))
            v = qs_sqrt(qk.c[1] - u * u)
            (v === nothing || iszero(v)) && break
            push!(pairs, (u, v))
        end
        length(pairs) == 2 || continue
        T2 = change_constants(T, S, c -> cfromQ(S, c))
        φ3(c) = B3(QI(c, Q(0)), zero(QI))
        T3 = change_constants(T, B3, φ3)
        K2, K3 = T2.Ts[i], T3.Ts[i]
        up(p) = UPoly{K3}(K3[change_constants(T, T3, c, φ3) for c in p.c])
        cj(c) = B3(QI(c.a.re, -c.a.im), QI(c.b.re, -c.b.im))
        ψ(c) = (iszero(c.a.im) && iszero(c.b.im)) ? S(c.a.re, c.b.re) : throw(RischError(
            "real form at a tower level: a conjugation-invariant coefficient is not real"))
        half = lconst(T3, B3(QI(Q(1) // 2, Q(0)), zero(QI)), i - 1)
        inv2i = lconst(T3, inv(B3(QI(Q(0), Q(2)), zero(QI))), i - 1)
        logs, atans = Any[], Any[]
        corr = zero(S)
        ok = true
        for (u, v) in pairs
            W = gcd(up(Dn), up(A) - scale(lconst(T3, B3(QI(u.a, v.a), QI(u.b, v.b)), i - 1), up(dD)))
            if degree(W) <= 0
                ok = false
                break
            end
            Uc, Vc = K2[], K2[]
            for w in W.c
                wc = change_constants(T3, T3, w, cj)
                push!(Uc, change_constants(T3, T2, (w + wc) * half, ψ))
                push!(Vc, change_constants(T3, T2, (w - wc) * inv2i, ψ))
            end
            U, V = UPoly{K2}(Uc), UPoly{K2}(Vc)
            if !iszero(u)
                w = U * U + V * V
                push!(logs, (u, frac(w)))
                corr = corr + degree(w) * u
            end
            if !iszero(U) && !iszero(V)
                for p in log_to_atan(U, V)
                    push!(atans, (2 * v, frac(p)))
                end
            end
        end
        ok || continue
        tot = zero(T2.Ts[i + 1])
        for (c, w) in logs
            tot = tot + lconst(T2, c, i) * (D(T2, i, w) / w)
        end
        for (c, p) in atans
            tot = tot + lconst(T2, c, i) * D(T2, i, p) / (one(p) + p * p)
        end
        down(c) = iszero(c.b) ? c.a : throw(RischError("real form at a tower level: derivative not over ℚ"))
        return TowerRealForm(T2, logs, atans, down(corr), change_constants(T2, T, tot, down))
    end
    nothing
end

# --- RootSums inside towers (step RT) ---------------------------------------------
# At level i (θ = θᵢ, K = Kᵢ₋₁): Σ_{m(α)=0} α log W(α, θ), W = gcd(D, A - α δD) in (K[z]/m)[θ]
# monic in θ (`d5_gcd` over K: ℚ is algebraically closed in K, so a split of m is over ℚ). W is
# stored θ-major (W[k]: coefficient of θ^(k-1), a polynomial in z over K, reduced mod m). The
# exact derivative is computed as for the base (`rootsum_derivative`), with the tower derivation:
#   δW = Σ_k (δc_k) θ^(k-1) + ∂_θW · Dθ   (z is a constant),   Σ α δW/W = Tr(z·δW·N/W)/N.
struct TowerRootSum
    i::Int
    mq::UPoly                # m, monic, over the constant field C (ℚ or ℚ(i))
    W::Vector{Any}           # Vector{UPoly{K}}
    deriv::Any               # exact derivative ∈ Kᵢ
end
# a base-level RootSum (in x) inside a tower; W in x as in `RootSum`
struct BaseRootSum
    rs::RootSum
    deriv::Any               # ∈ K₀ = ℚ(x)
end
# exp correction: Σ_α α·deg_θ W = Tr(α)·deg W
rootsum_corr(q::TowerRootSum) = (length(q.W) - 1) * (-q.mq.c[end - 1])

function tower_root_sums(T::Tower{C}, i::Int, A::UPoly{K}, D::UPoly{K}, dD::UPoly{K}, rest::UPoly{C}) where {C,K}
    P = UPoly{K}
    mK = P(K[lconst(T, c, i - 1) for c in monic(rest).c])
    n = max(length(A.c), length(dD.c))
    ai(k) = k <= length(A.c) ? A.c[k] : zero(K)
    di(k) = k <= length(dD.c) ? dD.c[k] : zero(K)
    a = P[P(K[c]) for c in D.c]
    b = P[P(K[ai(k), -di(k)]) for k in 1:n]             # A - z δD
    out = Any[]
    lr = lrt_logs(mK, D, A, dD)
    for (m, W) in (lr === nothing ? d5_gcd(mK, a, b) : lr)
        length(W) >= 2 || throw(RischError("RootSum: trivial gcd for a residue factor"))
        cs = C[]
        for c in m.c
            v = dconst_value(T, c)
            v === nothing && throw(RischNotImplemented("RootSum: a split of the residue polynomial is not over C"))
            push!(cs, v)
        end
        mq = UPoly{C}(cs)
        push!(out, TowerRootSum(i, mq, W, tower_rootsum_derivative(T, i, m, mq, W)))
    end
    out
end

function tower_rootsum_derivative(T::Tower, i::Int, m::UPoly{K}, mq::UPoly, W::Vector) where {K}
    P = UPoly{K}
    F = T.Ts[i + 1]                                     # Kᵢ
    θ = xpoly(K)
    nz = degree(m)
    # norm N(θ) = Π_α W(α, θ) = res_z(m, W(z, θ)) (m monic): degree ≤ deg m · deg_θ W in θ, so it is
    # interpolated from resultants over K at θ = 0, 1, 2, … (Euclid over Kᵢ = K(θ) swells, step ST)
    θs, vals = K[], K[]
    for t in 0:(nz * (length(W) - 1))
        θ0 = t * one(K)
        Wt = P(K[sum((j <= length(W[k].c) ? W[k].c[j] : zero(K)) * θ0^(k - 1) for k in eachindex(W)) for j in 1:nz])
        push!(θs, θ0)
        push!(vals, resultant(m, Wt))
    end
    N = interpolate(θs, vals)
    rest = P[P(K[c]) for c in N.c]                                    # N = W · cof mod m
    cof = [zero(P) for _ in 1:(length(rest) - length(W) + 1)]
    while length(rest) >= length(W)
        c = rest[end]
        s = length(rest) - length(W)
        cof[s + 1] = c
        for k in eachindex(W)
            rest[s + k] = rest[s + k] - c * W[k]
        end
        rest = zmod_trim(m, rest)
    end
    isempty(rest) || throw(RischError("RootSum: W(α, θ) does not divide its norm"))
    dθ = T.levels[i].dtheta
    dW = [P(K[D(T, i - 1, e) for e in W[k].c]) for k in eachindex(W)]
    for k in 2:length(W), (l, e) in enumerate(dθ.c)
        idx = k - 2 + l
        while length(dW) < idx
            push!(dW, zero(P))
        end
        dW[idx] = dW[idx] + scale(e * lq(T, Q(k - 1), i - 1), W[k])
    end
    dW = zmod_trim(m, dW)
    zP = P(K[zero(K), one(K)])
    ps = [lconst(T, c, i - 1) for c in power_sums(mq)]
    num = zero(P)
    for (a, u) in enumerate(dW), (b, v) in enumerate(cof)
        num = num + scale(ztrace(ps, rem(zP * u * v, m)), θ^(a + b - 2))
    end
    frac(num, N)
end

"""
    TermRootSum

`Σ_{Q(α)=0} α log W(α)` with `W(α) = Σ_j coeffs[j] α^(j-1)`, the `coeffs` being terms of the
user's package (a RootSum found inside a tower, e.g. in log(x)). `rs(a)` evaluates numerically
at x = a.
"""
struct TermRootSum
    poly::UPoly              # over ℚ, or ℚ(i) (then each coefficient is a pair (re, im) of terms)
    coeffs::Vector{Any}
    var::String
    pterms::Any              # nothing, or the coefficients of poly as terms (constants e, log 2, …)
end
TermRootSum(poly, coeffs, var) = TermRootSum(poly, coeffs, var, nothing)

# a base-level RootSum over C = ℚ(t₁, …) as a TermRootSum (step RE): α-coefficients are polynomials
# in x over C, printed with `poly_term`; the polynomial's coefficients are terms too
function base_term_rootsum(b::Builder, rs::RootSum{C}) where {C}
    xp = xpoly(C)
    cs = Any[]
    for j in 1:degree(rs.poly)
        p = sum((j <= length(rs.W[k].c) ? scale(rs.W[k].c[j], xp^(k - 1)) : zero(UPoly{C})) for k in eachindex(rs.W))
        push!(cs, iszero(p) ? nothing : poly_term(b, p))
    end
    TermRootSum(rs.poly, cs, string(b.x), Any[cterm(b, c) for c in rs.poly.c])
end
function TermRootSum(b::Builder, T::Tower, q::TowerRootSum)
    C = ctype(T)
    pt = (C === Q || C === QI) ? nothing : Any[cterm(b, c) for c in q.mq.c]
    K = T.Ts[q.i]
    P = UPoly{K}
    W = q.W
    cs = Any[]
    for j in 1:degree(q.mq)
        cz = P(K[j <= length(W[k].c) ? W[k].c[j] : zero(K) for k in eachindex(W)])
        push!(cs, iszero(cz) ? nothing : tower_to_term(b, T, frac(cz)))
    end
    TermRootSum(q.mq, cs, string(b.x), pt)
end

# a RootSum over ℚ(i) (trig tower, step RC): each α-coefficient w (an element of level i, or of
# ℚ(i)(x) for a base-level RootSum) is written as R + i·I with R = (w + σw)/2, I = (w - σw)/(2i)
# σ-invariant, i.e. real terms (`real_term`)
function complex_term_rootsum(b::Builder, T::Tower, kinds, q)
    C = ctype(T)
    if q isa BaseRootSum
        i, mq, W = 0, q.rs.poly, q.rs.W
        xp = xpoly(C)
        ws = [frac(sum((j <= length(W[k].c) ? scale(W[k].c[j], xp^(k - 1)) : zero(UPoly{C})) for k in eachindex(W)))
              for j in 1:degree(mq)]
    else
        i, mq, W = q.i, q.mq, q.W
        K = T.Ts[i]
        ws = [frac(UPoly{K}(K[j <= length(W[k].c) ? W[k].c[j] : zero(K) for k in eachindex(W)])) for j in 1:degree(mq)]
    end
    half = lconst(T, inv(cfromQ(C, Q(2))), i)
    inv2i = lconst(T, inv(cimag(C) + cimag(C)), i)
    cs = Any[]
    for w in ws
        sw = tconj(T, kinds, w, i)
        R, I = (w + sw) * half, (w - sw) * inv2i
        push!(cs, (iszero(R) ? nothing : real_term(b, T, kinds, R, i), iszero(I) ? nothing : real_term(b, T, kinds, I, i)))
    end
    TermRootSum(mq, cs, string(b.x))
end

# --- printing and numeric evaluation ---------------------------------------------
function zpoly_string(p::UPoly, v::String)
    ts = String[]
    for (k, c) in enumerate(p.c)
        iszero(c) && continue
        mon = k == 1 ? "" : (k == 2 ? v : "$v^$(k - 1)")
        cs = c isa Rational ? (isone(denominator(c)) ? string(numerator(c)) :
                               "$(numerator(c))/$(denominator(c))") :
             c isa QI ? (iszero(c.im) ? zpoly_string(UPoly{Q}([c.re]), "") :
                         "(" * zpoly_string(UPoly{Q}([c.re, c.im]), "im") * ")") : string(c)
        push!(ts, mon == "" ? cs : (isone(c) ? mon : (c == -1 ? "-" * mon : cs * "*" * mon)))
    end
    isempty(ts) ? "0" : replace(join(reverse(ts), " + "), "+ -" => "- ")
end
function Base.show(io::IO, rs::RootSum)
    x = rs.var
    ts = String[]
    for (k, c) in enumerate(rs.W)
        iszero(c) && continue
        cs = zpoly_string(c, "α")
        mon = k == 1 ? "" : (k == 2 ? x : "$x^$(k - 1)")
        push!(ts, mon == "" ? "($cs)" : (isone(c) ? mon : "($cs)*$mon"))
    end
    print(io, "RootSum(α -> α*log(", join(reverse(ts), " + "), "), ", zpoly_string(rs.poly, "α"), " = 0)")
end
function Base.show(io::IO, F::IntegralWithRootSums)
    ts = Any[rs for rs in F.rootsums]
    string(F.elementary) == "0" || pushfirst!(ts, F.elementary)
    join(io, ts, " + ")
end

# all complex roots of a polynomial with complex coefficients (Aberth–Ehrlich iteration)
function numeric_roots(cs::Vector{ComplexF64})
    n = length(cs) - 1
    cs = cs ./ cs[end]
    r = 1 + maximum(abs.(cs[1:n]))
    zs = [r * cis(2π * (k + 0.25) / n) for k in 0:(n - 1)]
    pv(z) = foldr((c, acc) -> acc * z + c, cs)
    dv(z) = foldr((c, acc) -> acc * z + c, [k * cs[k + 1] for k in 1:n]; init = 0.0im)
    for _ in 1:500
        δmax = 0.0
        for i in 1:n
            z = zs[i]
            w = pv(z) / dv(z)
            s = sum(1 / (z - zs[j]) for j in 1:n if j != i; init = 0.0im)
            δ = w / (1 - w * s)
            zs[i] = z - δ
            δmax = max(δmax, abs(δ))
        end
        δmax < 1e-15 * r && break
    end
    zs
end

cnum(c::Q) = ComplexF64(Float64(c))
cnum(c::QI) = ComplexF64(Float64(c.re), Float64(c.im))
cnum(c) = throw(RischNotImplemented("numeric evaluation of constants of type $(typeof(c))"))
cpoly_at(p::UPoly, z) = foldr((c, acc) -> acc * z + cnum(c), p.c; init = 0.0im)

function (rs::RootSum)(a::Number)
    tot = 0.0im
    for α in numeric_roots(ComplexF64[cnum(c) for c in rs.poly.c])
        w = foldr((c, acc) -> acc * a + cpoly_at(c, α), rs.W; init = 0.0im)
        tot += α * log(w)
    end
    tot
end

# numeric value of a term of the user's package at x = a (TermInterface walk)
function term_value(t, xk::String, a)
    if safe_iscall(t)
        args = arguments(t)
        if !isempty(args)
            vs = [term_value(s, xk, a) for s in args]
            n = opname(operation(t))
            f = haskey(OPS, n) ? OPS[n] : (n === :- ? (-) : operation(t))
            return ComplexF64(f(vs...))
        end
    end
    string(t) == xk && return ComplexF64(a)
    is_e_const(t) && return ComplexF64(ℯ)
    string(t) in ("pi", "π") && return ComplexF64(π)
    r = leaf_rational(t)
    r === nothing && throw(RischError("cannot evaluate the leaf $t numerically"))
    ComplexF64(Float64(r))
end

function Base.show(io::IO, rs::TermRootSum)
    ts = String[]
    for (j, c) in enumerate(rs.coeffs)
        c isa Tuple && (c = coeff_string(c))
        c === nothing && continue
        push!(ts, j == 1 ? "($c)" : (j == 2 ? "($c)*α" : "($c)*α^$(j - 1)"))
    end
    ps = rs.pterms === nothing ? zpoly_string(rs.poly, "α") :
         join(reverse([k == 1 ? "($t)" : (isone(rs.poly.c[k]) ? "" : "($t)*") * (k == 2 ? "α" : "α^$(k - 1)")
                       for (k, t) in enumerate(rs.pterms) if !iszero(rs.poly.c[k])]), " + ")
    print(io, "RootSum(α -> α*log(", join(ts, " + "), "), ", ps, " = 0)")
end
# numeric coefficients of the RootSum polynomial
rs_poly_numeric(rs::TermRootSum, xk::String) =
    rs.pterms === nothing ? ComplexF64[cnum(c) for c in rs.poly.c] : ComplexF64[term_value(t, xk, 0.0) for t in rs.pterms]
coeff_string((r, i)::Tuple) = (r === nothing && i === nothing) ? nothing :
    join(filter(!isempty, [r === nothing ? "" : string(r), i === nothing ? "" : "im*($i)"]), " + ")
cvalue(c, xk, a) = c === nothing ? 0.0im :
    c isa Tuple ? cvalue(c[1], xk, a) + im * cvalue(c[2], xk, a) : term_value(c, xk, a)
function rs_value(rs::TermRootSum, xk::String, a)
    vs = [cvalue(c, xk, a) for c in rs.coeffs]
    tot = 0.0im
    for α in numeric_roots(rs_poly_numeric(rs, xk))
        tot += α * log(foldr((v, acc) -> acc * α + v, vs; init = 0.0im))
    end
    tot
end
rs_value(rs::RootSum, xk::String, a) = rs(rs.arg === nothing ? a : term_value(rs.arg, xk, a))
(rs::TermRootSum)(a::Number) = rs_value(rs, rs.var, a)

# --- continuous evaluation (step RN) -----------------------------------------------
# A principal log W(α, x) jumps by 2πi where W crosses the negative real axis, and α·2πi then
# shifts Re F by -2π Im α. F(a) instead continues each log along [x₀, a] from a fixed reference
# point x₀ (the first of a few candidates where every W is finite and nonzero): the phase change
# is accumulated in steps refined until each is < 0.5 rad. This changes F only by constants on
# intervals, so it is still an antiderivative, now continuous.

# numeric roots α and a closure x -> [W(α, x) for each α]
function rs_numeric(rs::RootSum, xk::String)
    αs = numeric_roots(ComplexF64[cnum(c) for c in rs.poly.c])
    Wf(x) = (t = rs.arg === nothing ? ComplexF64(x) : term_value(rs.arg, xk, x);
             [foldr((c, acc) -> acc * t + cpoly_at(c, α), rs.W; init = 0.0im) for α in αs])
    αs, Wf
end
function rs_numeric(rs::TermRootSum, xk::String)
    αs = numeric_roots(rs_poly_numeric(rs, xk))
    Wf(x) = (vs = [cvalue(c, xk, x) for c in rs.coeffs];
             [foldr((v, acc) -> acc * α + v, vs; init = 0.0im) for α in αs])
    αs, Wf
end

const RS_REFERENCE_POINTS = (1.0, 2.0, 0.5, 3.0, 0.0, -1.0, 5.0, 10.0)

w_ok(w) = all(z -> isfinite(z) && abs(z) > 1e-12, w)
function safe_W(Wf, x)
    try
        Wf(x)
    catch
        nothing
    end
end

# phases of W(α, ·) continued from s (phases θ, values ws) to t
function continue_phase(Wf, s, t, ws, θ, depth::Int = 0)
    wt = safe_W(Wf, t)
    # a zero of W on the path is a pole of the integrand (F has a log singularity there): step over it
    (wt === nothing || !w_ok(wt)) && return θ, ws
    d = angle.(wt ./ ws)
    if maximum(abs, d) > 0.5 && depth < 40
        m = (s + t) / 2
        θ, wm = continue_phase(Wf, s, m, ws, θ, depth + 1)
        return continue_phase(Wf, m, t, wm, θ, depth + 1)
    end
    θ .+ d, wt
end

function rs_value_continuous(rs, xk::String, a::Real)
    αs, Wf = rs_numeric(rs, xk)
    x0 = nothing
    w0 = nothing
    for c in RS_REFERENCE_POINTS
        w = safe_W(Wf, c)
        if w !== nothing && w_ok(w)
            x0, w0 = c, w
            break
        end
    end
    x0 === nothing && return rs_value(rs, xk, a)        # no reference point found: principal logs
    θ, w = angle.(w0), w0
    n = max(8, ceil(Int, 8 * abs(a - x0)))
    xs = range(x0, a; length = n + 1)
    for k in 2:length(xs)
        θ, w = continue_phase(Wf, xs[k - 1], xs[k], w, θ)
    end
    sum(αs[k] * (log(abs(w[k])) + im * θ[k]) for k in eachindex(αs); init = 0.0im)
end

(F::IntegralWithRootSums)(a::Real) =
    real(term_value(F.elementary, F.var, a) +
         sum(rs_value_continuous(rs, F.var, a) for rs in F.rootsums; init = 0.0im))

# ---------------------------------------------------------------------------
# Step TS: simpler trigonometric forms by Bioche's rules
#
# f rational in sin u, cos u (u = k x): in the ℚ(i) tower f = R(θ), θ = e^{iu}, R with constant
# coefficients. If the form ω = R du is invariant under
#   u ↦ -u      (R(1/θ) = -R(θ)):   s = cos u,  du/ds = -1/sin u = -2iθ/(θ² - 1)
#   u ↦ π - u   (R(-1/θ) = -R(θ)):  s = sin u,  du/ds = 1/cos u = 2θ/(θ² + 1)
#   u ↦ π + u   (R(-θ) = R(θ)):     s = tan u,  θ² = (1 + is)/(1 - is), du/ds = 1/(1 + s²)
# then ω = g(s) ds with g ∈ ℚ(s) (a function invariant under θ ↦ 1/θ is a rational function of
# (θ + 1/θ)/2, via θʲ + θ⁻ʲ = 2Tⱼ; for sin, θ = iη reduces to the cos case). g(s(θ))·s′ = f is
# checked exactly in the tower and ∫ g ds exactly in ℚ(s) (`check_result`), so the answer G(s(x))
# is verified by the chain rule. The rational integral has atans of polynomials (R3), so G(cos u),
# G(sin u) are continuous; G(tan u) jumps where tan u = ±∞: each c·atan(p) with p of odd degree and
# lc sign σ jumps by -cσπ, corrected by J(u - atan(tan u)) = Jπ⌊(u + π/2)/π⌋, J = Σ cσ (no π).
# Returns a term, or nothing (not of this kind: the general route is used).
# ---------------------------------------------------------------------------
# polynomials over the constant field C = ℚ(i) or ℚ(i)(t₁, …) (step TE: generic in C)
# p(c/θ)·θ^deg p  and  p(cθ)
θinv_poly(p::UPoly{C}, c::C) where {C} = UPoly{C}(reverse(C[p.c[k] * field_pow(c, k - 1) for k in eachindex(p.c)]))
θscale_poly(p::UPoly{C}, c::C) where {C} = UPoly{C}(C[p.c[k] * field_pow(c, k - 1) for k in eachindex(p.c)])
function θinv(R::Frac{UPoly{C}}, c::C) where {C}       # R(c/θ)
    θ = xpoly(C)
    frac(θinv_poly(R.num, c) * θ^degree(R.den), θinv_poly(R.den, c) * θ^degree(R.num))
end
θscale(R::Frac{UPoly{C}}, c::C) where {C} = frac(θscale_poly(R.num, c), θscale_poly(R.den, c))

# θ^(-sh)·M = Σ aⱼ θʲ, symmetric (aⱼ = a₋ⱼ), as a polynomial in s = (θ + 1/θ)/2, or nothing
function sym_laurent_to_s(M::UPoly{C}, sh::Int) where {C}
    n = degree(M) - sh
    a(j) = 0 <= j + sh < length(M.c) ? M.c[j + sh + 1] : zero(C)
    all(k -> iszero(M.c[k]), 1:max(0, sh - n)) || return nothing    # lowest exponent ≥ -n
    all(j -> a(j) == a(-j), 1:n) || return nothing
    P = UPoly{C}
    Tm, Tc = one(P), xpoly(C)                            # T₀, T₁
    out = scale(a(0), one(P))
    for j in 1:n
        out = out + scale(2 * a(j), Tc)
        Tm, Tc = Tc, scale(cfromQ(C, Q(2)), xpoly(C)) * Tc - Tm
    end
    out
end
# h(θ) with h(1/θ) = h(θ) as a rational function of s = (θ + 1/θ)/2
function sym_to_s(h::Frac{UPoly{C}}) where {C}
    Dr = θinv_poly(h.den, one(C))
    P = sym_laurent_to_s(h.num * Dr, degree(h.den))
    Qd = sym_laurent_to_s(h.den * Dr, degree(h.den))
    (P === nothing || Qd === nothing) ? nothing : frac(P, Qd)
end
# R(θ) = R̃(θ²): g(s) = R̃((1 + is)/(1 - is))/(1 + s²)
function tan_to_s(R::Frac{UPoly{C}}) where {C}
    N, D = R.num, R.den
    par(p) = all(k -> iszero(p.c[k]) || iseven(k - 1), eachindex(p.c)) ? 0 :
             all(k -> iszero(p.c[k]) || isodd(k - 1), eachindex(p.c)) ? 1 : nothing
    pn, pd = par(N), par(D)
    (pn === nothing || pn != pd) && return nothing
    half(p) = [p.c[k] for k in (1 + pn):2:length(p.c)]   # coefficients of ζ^0, ζ^1, … in p/θ^pn
    nc, dc = half(N), half(D)
    n = max(length(nc), length(dc)) - 1
    I = cimag(C)
    P = UPoly{C}
    ap, am = P(C[one(C), I]), P(C[one(C), -I])
    hom(cs) = sum(scale(cs[k + 1], ap^k * am^(n - k)) for k in 0:(length(cs) - 1))
    frac(hom(nc), hom(dc) * P(C[one(C), zero(C), one(C)]))
end

# the real field of C: ℚ(i) -> ℚ, ℚ(i)(t₁, …) -> ℚ(t₁, …) (real generators e^a, log p)
real_ctype(::Type{QI}) = Q
real_ctype(::Type{Frac{UPoly{B}}}) where {B} = Frac{UPoly{real_ctype(B)}}
# c ∈ C with real coefficients (normal form is unique, so a real constant has them) in the real
# field, or nothing
to_real(c::QI) = iszero(c.im) ? c.re : nothing
function to_real(c::Frac{UPoly{B}}) where {B}
    RB = real_ctype(B)
    n, d = [to_real(a) for a in c.num.c], [to_real(a) for a in c.den.c]
    (any(isnothing, n) || any(isnothing, d)) && return nothing
    Frac{UPoly{RB}}(UPoly{RB}(RB[n...]), UPoly{RB}(RB[d...]))
end
to_complex(::Type{Frac{UPoly{B}}}, r::Frac) where {B} =
    Frac{UPoly{B}}(UPoly{B}(B[to_complex(B, a) for a in r.num.c]), UPoly{B}(B[to_complex(B, a) for a in r.den.c]))

# sign of a real constant: exact over ℚ; over ℚ(t₁, …) from a 256-bit evaluation of the generators
# (e^a, log p), and nothing (undecided) if the value is within 1e-40 of 0. Only used to choose a
# form (no pole in range, sign of a log argument), never for the answer itself.
cdepth(::Type{Q}) = 0
cdepth(::Type{Frac{UPoly{B}}}) where {B} = 1 + cdepth(B)
cbig(c::Q, gens) = BigFloat(c)
function cbig(c::Frac{UPoly{B}}, gens) where {B}
    g = gens[cdepth(typeof(c))]
    t = g.kind === :exp ? exp(BigFloat(g.arg)) : log(BigFloat(g.arg))
    pe(p) = foldr((a, acc) -> acc * t + cbig(a, gens), p.c; init = BigFloat(0))
    pe(c.num) / pe(c.den)
end
csign(c::Q, gens) = Int(sign(c))
function csign(c, gens)
    iszero(c) && return 0
    v = setprecision(() -> cbig(c, gens), BigFloat, 256)
    abs(v) < big(10)^-40 ? nothing : Int(sign(v))
end

# number of distinct real roots of p ∈ R[s] in [a, b] (a = nothing: -∞, b = nothing: +∞), Sturm;
# sg is the sign function of the real field R (nothing: undecided, then the result is nothing)
function real_root_count(p::UPoly{R}, a, b, sg = c -> Int(sign(c))) where {R}
    degree(p) <= 0 && return 0
    p = quo(p, gcd(p, deriv(p)))
    seq = UPoly{R}[p, deriv(p)]
    while degree(seq[end]) > 0
        r = -rem(seq[end - 1], seq[end])
        iszero(r) && break
        push!(seq, r)
    end
    at(q, x) = peval(q, cfromQ(R, Q(x)))
    sgn(q, x) = x === nothing ? sg(lc(q)) : sg(at(q, x))
    sgninf(q, side) = (s = sg(lc(q)); s === nothing ? nothing : side < 0 && isodd(degree(q)) ? -s : s)
    function changes(vals)
        any(isnothing, vals) && return nothing
        v = filter(!iszero, vals)
        count(k -> v[k] != v[k + 1], 1:(length(v) - 1))
    end
    va = changes([a === nothing ? sgninf(q, -1) : sgn(q, a) for q in seq])
    vb = changes([b === nothing ? sgninf(q, 1) : sgn(q, b) for q in seq])
    (va === nothing || vb === nothing) && return nothing
    va - vb + ((a !== nothing && iszero(at(p, a))) ? 1 : 0)     # roots in (a, b], plus a
end

# x-jump coefficient of an atan argument p(s) at s = ±∞ (Σ c σ for odd degree), as a real sign
function atan_infinity_sign(p::Frac)
    d = degree(p.num) - degree(p.den)
    (d > 0 && isodd(d)) || return 0
    Int(real_sign(lc(p.num) / lc(p.den)))
end

function bioche(f, x; build = nothing, lift = nothing)
    xk = string(x)
    T, el = try
        build_tower(f, xk)
    catch e
        e isa RischNotImplemented && return nothing
        rethrow()
    end
    C = ctype(T)
    # C = ℚ(i), or ℚ(i)(t₁, …) with real generators e^a, log p (step TE)
    (C === QI || (C <: Frac && cbase(C) === QI && all(g -> g.kind in (:exp, :log), T.consts))) || return nothing
    (length(T.levels) == 1 && T.levels[1].kind === :exp) || return nothing
    RC = real_ctype(C)
    I = cimag(C)
    a = T.levels[1].arg
    (isone(a.den) && degree(a.num) == 1 && iszero(a.num.c[1])) || return nothing
    kr = to_real(a.num.c[2] * inv(I))
    k = kr === nothing ? nothing : kr isa Q ? kr : crational(kr)
    k === nothing && return nothing                      # θ = e^{iu}, u = k x, k ∈ ℚ
    levelof(T, el) == 1 || return nothing
    cs(p) = (v = [const_value(T, c) for c in p.c]; any(isnothing, v) ? nothing : UPoly{C}(C[c for c in v]))
    N, Dn = cs(el.num), cs(el.den)
    (N === nothing || Dn === nothing) && return nothing
    R = frac(N, Dn)
    P = UPoly{C}
    two = cfromQ(C, Q(2))
    θp = xpoly(C)
    K1 = T.Ts[1]
    θel = frac(xpoly(K1))
    one1 = one(θel)
    li(c) = lconst(T, c, 1)
    if θinv(R, one(C)) == -R                             # s = cos u
        kind = :cos
        g = sym_to_s(R * frac(scale(-2 * I, θp), θp^2 - one(P)))
        sel = (θel + one1 / θel) * li(inv(two))
    elseif θinv(R, -one(C)) == -R                        # s = sin u
        kind = :sin
        g = sym_to_s(θscale(R * frac(scale(two, θp), θp^2 + one(P)), I))
        sel = (θel - one1 / θel) * li(inv(2 * I))
    elseif θscale(R, -one(C)) == R                       # s = tan u
        kind = :tan
        g = tan_to_s(R)
        sel = li(-I) * (θel * θel - one1) / (θel * θel + one1)
    else
        return nothing
    end
    g === nothing && return nothing
    g = g * kconst(inv(cfromQ(C, k)))                    # dx = du/k
    rn, rd = [to_real(c) for c in g.num.c], [to_real(c) for c in g.den.c]
    (any(isnothing, rn) || any(isnothing, rd)) && return nothing
    gq = frac(UPoly{RC}(RC[rn...]), UPoly{RC}(RC[rd...]))
    # the substitution, exactly: g(s(θ))·ds/dx = f
    gs(p) = foldr((c, acc) -> acc * sel + li(to_complex(C, c)), p.c; init = zero(sel))
    gs(gq.num) / gs(gq.den) * D(T, 1, sel) == liftto(T, el, 1) ||
        throw(RischError("internal check failed: Bioche substitution"))
    # real poles of f (poles of g in the range of s) → the general route (real forms with |w|²)
    sg(c) = csign(c, T.consts)
    rng = kind === :tan ? (nothing, nothing) : (-1, 1)
    real_root_count(gq.den, rng..., sg) == 0 || return nothing
    res = integrate_rational(gq)
    # residues of degree > 2 (step TR): a RootSum in s = cos u or sin u (over ℚ, real and continuous
    # since g has no pole in [-1, 1]); for s = tan u see step TT below
    unres = res.unresolved
    # step TB: for s = tan u without RootSums, the general route (TC/TH) gives a linear term plus atans
    # of trigonometric ratios with nonvanishing denominators (no tan, no correction terms); use it when
    # it is elementary and needed no tan(u/2) form, else the tan form below
    if kind === :tan && isempty(unres)
        HALF_ANGLE_FORMS[] = 0
        r = try
            Tg, elg = build_tower(f, xk)
            bdg = Builder(build === nothing ? auto_build(f, x) : build, lift === nothing ? auto_lift(f, x) : lift, x, Tg.consts)
            integrate_built(Tg, elg, bdg, true)
        catch e
            (e isa RischNotImplemented || e isa NotElementary) || rethrow()
            nothing
        end
        (r === nothing || r isa IntegralWithRootSums || HALF_ANGLE_FORMS[] > 0) || return r
    end
    # each log argument has constant sign on the range: log(-w) where it is negative (at s = 0)
    w0s = [sg(peval(w, zero(RC))) for (c, w) in res.logs]
    any(isnothing, w0s) && return nothing
    logs = Tuple{RC,UPoly{RC}}[(c, w0 < 0 ? -w : w) for ((c, w), w0) in zip(res.logs, w0s)]
    # log((U + √dV)/(U - √dV)) with a negative ratio: the same as log((dV + √dU)/(dV - √dU))
    quads = Any[]
    for q in res.quads
        if q isa QuadLog
            u0, v0 = peval(q.U, Q(0)), peval(q.V, Q(0))
            neg = real_sign(QS{q.d}(u0, v0)) * real_sign(QS{q.d}(u0, -v0)) < 0
            q = neg ? QuadLog(q.β, q.d, q.d * q.V, q.U) : q
        end
        push!(quads, q)
    end
    res = RationalIntegral(res.rational, logs, res.atans, Any[], quads)
    bd = Builder(build === nothing ? auto_build(f, x) : build, lift === nothing ? auto_lift(f, x) : lift, x, T.consts)
    ut = isone(k) ? bd.x : mk(bd, :*, cterm(bd, k), bd.x)
    st = mk(bd, kind, ut)
    bs = Builder(bd.build, bd.lift, st, T.consts)       # prints s as sin(kx), cos(kx), tan(kx)
    if !isempty(unres)
        rss = Any[]
        for (rest, R, Dd) in unres
            append!(rss, root_sums(rest, R, Dd, string(st); arg = st))
        end
        derivative_of(res) + sum(rootsum_derivative(rs) for rs in rss) == gq ||
            throw(RischError("internal check failed: derivative of the result (with RootSums) differs from the integrand"))
        if kind !== :tan
            rss = RC === Q ? rss : Any[base_term_rootsum(bs, rs) for rs in rss]
            return IntegralWithRootSums(to_term(bs, res), rss, xk)
        end
        # step TT: W(α, tan u) = cos(u)^(-n) W̃(α), W̃ = Σ w_k sin^k(u) cos^(n-k)(u), bounded and nonzero on
        # the real line (W monic: W̃ = ±1 where cos u = 0). So Σ α log W = Σ α log W̃ - (Σα) n log cos u,
        # the first continuous (F(a), step RN), the second real: -(Σα)·n/2·log(cos²u) (Σα ∈ RC since
        # m has coefficients in RC); its log singularity cancels against the logs in tan u, and the
        # atan jumps are corrected below as for elementary answers
        sin_t, cos_t = mk(bd, :sin, ut), mk(bd, :cos, ut)
        pw(t, e) = e == 1 ? t : mk(bd, :^, t, bd.lift(e))
        trs = Any[]
        clc = zero(RC)
        for rs in rss
            n = length(rs.W) - 1
            cs = Any[]
            for j in 1:degree(rs.poly)
                ts = Any[]
                for kk in eachindex(rs.W)
                    c = j <= length(rs.W[kk].c) ? rs.W[kk].c[j] : zero(RC)
                    iszero(c) && continue
                    mono = Any[]
                    kk - 1 > 0 && push!(mono, pw(sin_t, kk - 1))
                    n - kk + 1 > 0 && push!(mono, pw(cos_t, n - kk + 1))
                    t = isempty(mono) ? cterm(bs, c) :
                        isone(c) ? (length(mono) == 1 ? mono[1] : mk(bd, :*, mono...)) : mk(bd, :*, cterm(bs, c), mono...)
                    push!(ts, t)
                end
                push!(cs, isempty(ts) ? nothing : length(ts) == 1 ? ts[1] : mk(bd, :+, ts...))
            end
            push!(trs, TermRootSum(rs.poly, cs, xk, RC === Q ? nothing : Any[cterm(bs, c) for c in rs.poly.c]))
            clc = clc + n * (-rs.poly.c[end - 1])          # (Σα)·n, m monic
        end
        parts = Any[to_term(bs, res)]
        corr = tan_jump_terms(bd, bs, res)
        isempty(corr) || push!(parts, mk(bd, :*, length(corr) == 1 ? corr[1] : mk(bd, :+, corr...),
                                         mk(bd, :+, ut, mk(bd, :*, bd.lift(-1), mk(bd, :atan, mk(bd, :tan, ut))))))
        iszero(clc) || push!(parts, mk(bd, :*, cterm(bs, -clc / cfromQ(RC, Q(2))), mk(bd, :log, mk(bd, :^, cos_t, bd.lift(2)))))
        return IntegralWithRootSums(length(parts) == 1 ? parts[1] : mk(bd, :+, parts...), trs, xk)
    end
    check_result(res, gq) || throw(RischError("internal check failed: derivative of the result differs from the integrand"))
    term = to_term(bs, res)
    kind === :tan || return term
    corr = tan_jump_terms(bd, bs, res)
    isempty(corr) && return term
    cc = length(corr) == 1 ? corr[1] : mk(bd, :+, corr...)
    mk(bd, :+, term, mk(bd, :*, cc, mk(bd, :+, ut, mk(bd, :*, bd.lift(-1), mk(bd, :atan, mk(bd, :tan, ut))))))
end

# the jumps of G(tan u) where tan u = ±∞: coefficient terms J with correction J·(u - atan(tan u))
function tan_jump_terms(bd::Builder, bs::Builder, res::RationalIntegral)
    corr = Any[]
    J = Q(0)
    for (c, p) in res.atans
        J += c * atan_infinity_sign(p)
    end
    iszero(J) || push!(corr, cterm(bd, J))
    for q in res.quads
        if q isa QuadAtan
            σ = atan_infinity_sign(q.u)
            σ == 0 || push!(corr, mk(bd, :*, cterm(bd, q.c * σ), mk(bd, :sqrt, bd.lift(q.e))))
        elseif q isa RationalIntegral
            Jd = sum((c * atan_infinity_sign(p) for (c, p) in q.atans); init = zero(typeof(q.rational.num.c[1])))
            iszero(Jd) || push!(corr, cterm(bd, Jd))
        end
    end
    corr
end

# ---------------------------------------------------------------------------
# Public API
# ---------------------------------------------------------------------------
function risch_integrate(f, x; build = nothing, lift = nothing, verify::Bool = true)
    xk = string(x)
    rads = collect_radicals(f, xk)
    if !isempty(rads)                  # a RootSum is in the substitution variable t: evaluate through x
        F = integrate_radical(f, x, rads; build = build, lift = lift, verify = verify)
        return F isa IntegralWithRootSums ? IntegralWithRootSums(F.elementary, F.rootsums, xk) : F
    end
    if has_trig(f)                     # polynomial × exp × trig first (Stage 5c), else the ℚ(i) tower
        try
            return integrate_trig(f, x; build = build, lift = lift, verify = verify)
        catch e
            e isa RischNotImplemented || rethrow()
        end
        r = bioche(f, x; build = build, lift = lift)    # rational in sin u, cos u (step TS)
        r === nothing || return r
    end
    T, el = build_tower(f, xk)
    bd = Builder(build === nothing ? auto_build(f, x) : build,
                 lift === nothing ? auto_lift(f, x) : lift, x, T.consts)
    integrate_built(T, el, bd, verify)
end

# integrate an element of a built tower and return the term (base variable printed as bd.x)
function integrate_built(T::Tower, el, bd::Builder, verify::Bool)
    L = length(T.levels)
    if is_complex_field(ctype(T))      # Step 7: integrate over ℚ(i), then take the real part
        res = integrate_el(T, L, el)
        verify && !check_tower(T, L, res, el) &&
            throw(RischError("internal check failed: derivative of the result differs from the integrand"))
        isrsc(q) = q isa TowerRootSum || q isa BaseRootSum
        any(isrsc, res.quads) || return to_term_real(bd, T, L, res, el)
        # step RC: RootSums over ℚ(i) stay complex (F(a) takes the real part); the elementary part
        # is put in real form and checked against f - Re(Σ RootSum′), Re = (d + σd)/2
        kinds = sigma_kinds(T)
        rss = Any[complex_term_rootsum(bd, T, kinds, q) for q in res.quads if isrsc(q)]
        drs = sum(liftto(T, q.deriv, L) for q in res.quads if isrsc(q))
        re = (drs + tconj(T, kinds, drs, L)) * lconst(T, inv(cfromQ(ctype(T), Q(2))), L)
        el_part = ElemIntegral(res.v, res.logs, res.atans, Any[q for q in res.quads if !isrsc(q)])
        return IntegralWithRootSums(to_term_real(bd, T, L, el_part, liftto(T, el, L) - re), rss, string(bd.x))
    end
    if L > 0
        res = integrate_el(T, L, el)
        verify && !check_tower(T, L, res, el) &&
            throw(RischError("internal check failed: derivative of the result differs from the integrand"))
        isrs(q) = q isa TowerRootSum || q isa BaseRootSum
        any(isrs, res.quads) || return to_term(bd, T, res)
        rss = Any[q isa BaseRootSum ?
                  (ctype(T) === Q ? RootSum{Q}(q.rs.poly, q.rs.W, string(bd.x), bd.x) : base_term_rootsum(bd, q.rs)) :
                  TermRootSum(bd, T, q) for q in res.quads if isrs(q)]
        el_part = ElemIntegral(res.v, res.logs, res.atans, Any[q for q in res.quads if !isrs(q)])
        return IntegralWithRootSums(to_term(bd, T, el_part), rss, string(bd.x))
    end
    F = el                              # an element of K_0 = C(x)
    res = integrate_rational(F)
    if !isempty(res.unresolved)
        C = ctype(T)
        (C === Q || rational_tfield(C)) || throw(RischNotImplemented(
            "the logarithmic part has residues of degree > 2 over the constant field $C " *
            "(RootSum is implemented over ℚ and ℚ(t₁, …) only)"))
        rss = RootSum[]                 # algebraic residues of degree > 2: RootSum
        for (rest, R, D) in res.unresolved
            append!(rss, root_sums(rest, R, D, string(bd.x); arg = bd.x))
        end
        el_part = RationalIntegral(res.rational, res.logs, res.atans, Any[], res.quads)
        verify && derivative_of(el_part) + sum(rootsum_derivative(rs) for rs in rss) != F &&
            throw(RischError("internal check failed: derivative of the result (with RootSums) differs from the integrand"))
        out = C === Q ? Any[rs for rs in rss] : Any[base_term_rootsum(bd, rs) for rs in rss]   # step RE
        return IntegralWithRootSums(to_term(bd, el_part), out, string(bd.x))
    end
    verify && !check_result(res, F) &&
        throw(RischError("internal check failed: derivative of the result differs from the integrand"))
    to_term(bd, res)
end

end # module
