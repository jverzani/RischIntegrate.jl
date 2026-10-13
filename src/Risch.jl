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
"""
module Risch

using TermInterface: iscall, operation, arguments

export risch_integrate, integrate_rational, tower_derivative, RischError, RischNotImplemented,
       NotElementary

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

function Base.gcd(a::UPoly{T}, b::UPoly{T}) where {T}
    while !iszero(b)
        a, b = b, rem(a, b)
    end
    monic(a)
end

# s*a + t*b = g, with g monic
function gcdex(a::UPoly{T}, b::UPoly{T}) where {T}
    P = typeof(a)
    r0, r1 = a, b
    s0, s1 = one(P), zero(P)
    t0, t1 = zero(P), one(P)
    while !iszero(r1)
        q, r = divrem(r0, r1)
        r0, r1 = r1, r
        s0, s1 = s1, s0 - q * s1
        t0, t1 = t1, t0 - q * t1
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

# Residues are the two roots a = α ± β√d of the irreducible quadratic `rest`. With
# W = gcd(D, A - a D') = U + √d V:   a log W + ā log W̄ is
#   α log(U² - d V²) + β√d log((U + √d V)/(U - √d V))                 (d > 1)
#   α log(U² + e V²) - 2β√e atan(√e V/U),   e = -d                     (d < 0)
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
            e = -dd
            if degree(V) == 0
                push!(quads, QuadAtan(2 * β, e, frac(U, V), true))
            else
                push!(quads, QuadAtan(-2 * β, e, frac(V, U), false))
            end
        end
    end
    logs, quads
end

function log_part(A::UPoly{C}, D::UPoly{C}) where {C}
    CXl = UPoly{C}
    CXFl = Frac{UPoly{C}}
    logs = Tuple{C,CXl}[]
    atans = Tuple{C,CXFl}[]
    unresolved = Any[]
    quads = Any[]
    iszero(A) && return logs, atans, unresolved, quads
    dD = deriv(D)
    # R(z) = res_x(D, A - z D') computed in the field C(z)
    Kz = CXFl
    n = max(length(A.c), length(dD.c))
    ai(i) = i <= length(A.c) ? A.c[i] : zero(C)
    di(i) = i <= length(dD.c) ? dD.c[i] : zero(C)
    Dz = UPoly{Kz}(Kz[kconst(c) for c in D.c])
    Bz = UPoly{Kz}(Kz[frac(CXl(C[ai(i), -di(i)])) for i in 1:n])
    r = resultant(Dz, Bz)
    iszero(r) && throw(RischError("zero resultant in the residue computation"))
    isone(r.den) || throw(RischError("residue polynomial is not a polynomial"))
    Rz = r.num
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
    handled = false
    if C === Q && degree(rest) == 2           # quadratic residues: ℚ only for now (steps 5/5b)
        rest = monic(rest)
        p0, p1 = rest.c[1], rest.c[2]
        α = -p1 / 2
        s = rat_sqrt(-(p1^2 - 4 * p0))      # sqrt(-discriminant), only if rational
        if s !== nothing && !iszero(s)
            β = s / 2
            a = QI(α, β)
            W = gcd(toQI(D), toQI(A) - scale(a, toQI(dD)))
            U = CXl(C[w.re for w in W.c])
            V = CXl(C[w.im for w in W.c])
            iszero(α) || push!(logs, (α, U * U + V * V))
            if !iszero(U) && !iszero(V)
                if degree(V) == 0
                    push!(atans, (2 * β, frac(U, V)))
                else
                    push!(atans, (-2 * β, frac(V, U)))
                end
            end
            handled = true
        end
        if !handled                          # irrational or non-square complex residues (5a)
            qt = quad_terms(A, D, dD, rest)
            if qt !== nothing
                append!(logs, qt[1])
                append!(quads, qt[2])
                handled = true
            end
        end
    end
    handled || push!(unresolved, (rest, A, D))
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
        if q isa QuadLog      # d/dx [β√d log(W/W̄)] = 2βd (V'U - U'V)/(U² - dV²)
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
                                  :sin => sin, :cos => cos)
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
    t = constgen_term(b, b.consts[k])
    n = cpoly_term(b, c.num, t)
    isone(c.den) ? n : mk(b, :/, n, cpoly_term(b, c.den, t))
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
        if q isa QuadLog
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
end
Tower(::Type{C}, xk::String, scales::Dict{Int,Int}, consts::Vector{ConstGen} = ConstGen[]) where {C} =
    Tower{C}(xk, Level[], DataType[Frac{UPoly{C}}], scales, 0, consts)
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
is_complex_field(::Type{C}) where {C} = C === QI || (C <: Frac && cbase(C) === QI)
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
    logs = [j for j in eachindex(gens) if gens[j].kind === :log]
    vs = cflat_all(C, C[one(C); C[tgen(C, j) for j in logs]; c])
    sol = solve_columns(vs[1:(end - 1)], vs[end])
    sol === nothing && throw(RischNotImplemented(
        "exp of the constant $c: only exp(rational + integer multiples of logs of rationals) is implemented"))
    val = one(C)
    for (j, ρ) in zip(logs, sol[2:end])
        iszero(ρ) && continue
        isone(denominator(ρ)) || throw(RischNotImplemented(
            "exp of a rational multiple of log $(gens[j].arg) is an algebraic number"))
        val = val * cfromQ(C, gens[j].arg^Int(numerator(ρ)))
    end
    a = sol[1]
    iszero(a) && return val
    jE = findfirst(g -> g.kind === :exp, gens)
    if jE === nothing                                       # first appearance of e: tₑ = e^(1/den a)
        throw(NewConstants(ConstGen[ConstGen(:exp, Q(1) // denominator(a)); gens]))
    end
    s = denominator(gens[jE].arg)                            # tₑ = e^(1/s)
    m = a * s
    if !isone(denominator(m))                               # refine: tₑ = e^(1/lcm(s, den a))
        g2 = copy(gens)
        g2[jE] = ConstGen(:exp, Q(1) // lcm(s, denominator(a)))
        throw(NewConstants(g2))
    end
    val * tgen(C, jE)^Int(numerator(m))
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
    if safe_iscall(t)
        args = arguments(t)
        if !isempty(args)
            n = opname(operation(t))
            if n in (:sin, :cos, :tan) && length(args) == 1     # Step 7: θ = exp(i·u) over ℚ(i)
                C = ctype(T)
                (C === QI || (C <: Frac && cbase(C) === QI)) || throw(NeedComplex())
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
function build_tower(f, xk::String; constants::Union{Nothing,Type} = nothing)
    scales = Dict{Int,Int}()
    consts = ConstGen[]
    base = Q                                   # becomes ℚ(i) when trigonometric functions appear
    for _ in 1:50
        C = constants === nothing ? cfield(length(consts), base) : constants
        T = Tower(C, xk, scales, copy(consts))
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
    a == -1 && throw(RischNotImplemented("RDE with a simple pole of f at infinity"))
    # denominator bound
    Dn = one(P)
    fparts = squarefree(Df)
    for (gk, k) in squarefree(Dg)
        remaining = gk
        for (fi, i) in fparts
            part = gcd(remaining, fi)
            degree(part) > 0 || continue
            i == 1 && throw(RischNotImplemented("RDE: f has a simple pole (cancellation case)"))
            Dn = Dn * part^max(0, k - i)
            remaining = quo(remaining, part)
        end
        Dn = Dn * remaining^max(0, k - 1)
    end
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
        return rde_base(f, g)
    end
    lv = T.levels[m]
    k = T.Ts[m]
    zk = zero(k)
    islog = lv.kind === :log
    fl = laurent_of(T, m, f, islog)
    gl = laurent_of(T, m, g, islog)
    isempty(fl) && throw(RischError("RDE with f = 0 is plain integration"))
    df, ef = maximum(keys(fl)), minimum(keys(fl))
    dg, eg = maximum(keys(gl)), minimum(keys(gl))
    c = Dict{Int,k}()
    if islog
        tp = lv.dtheta.c[1]
        if df == 0                                        # f ∈ k: triangular system of RDEs in k
            for i in dg:-1:0
                rhs = get(gl, i, zk) - (i + 1) * get(c, i + 1, zk) * tp
                ci = rde(T, m - 1, fl[0], rhs)
                ci === nothing && return nothing
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
        # Cancellation exponent: at exponent i the lowest/top equation reads
        # c' + (f_0 + i w') c = g_i, and f_0 + i w' = 0 for i0 = -f_0/w' when that is an
        # integer (e.g. u = x + t with t = exp(x) gives i0 = -1: exp(x + e^x) has the
        # antiderivative exp(e^x) = θ/t). There a constant c is a homogeneous solution,
        # so the support of y may extend to i0.
        i0 = nothing
        if !iszero(wp)
            cv = dconst_value(T, -get(fl, 0, zk) / wp)
            if cv !== nothing
                n0 = cinteger(cv)
                n0 === nothing || (i0 = Int(numerator(n0)))
            end
        end
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
            hi < lo && return nothing
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
            hi < lo && return nothing
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
    D(T, m, y) + f * y == g ? y : nothing
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
#                      = α log(U² + e V²) - 2β√e atan(√e V/U),   e = -d          (d < 0)
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
        elseif !iszero(U)
            e = -dd
            if degree(V) == 0
                push!(quads, TowerQuadAtan(2 * β, e, Uf / Vf, true))
            else
                push!(quads, TowerQuadAtan(-2 * β, e, Vf / Uf, false))
            end
        end
    end
    logs, quads
end

# R(z) = res_θ(D, A - z δD) must have constant roots. Returns (logs, quads): logs are
# [(c, W)] with W = gcd(D, A - c δD) ∈ Kᵢ₋₁[θ] (also the α log(U² - dV²) terms of a quadratic
# pair: for the exp correction Σ c·deg W they count exactly like the two conjugate logs), and
# quads the TowerQuadLog / TowerQuadAtan terms of irreducible quadratic residue factors.
function residue_logs(T::Tower, i::Int, A::UPoly, D::UPoly)
    K = T.Ts[i]
    Kz = Frac{UPoly{K}}
    dD = Dp(T, i, D)
    n = max(length(A.c), length(dD.c))
    ai(k) = k <= length(A.c) ? A.c[k] : zero(K)
    di(k) = k <= length(dD.c) ? dD.c[k] : zero(K)
    Dz = UPoly{Kz}(Kz[frac(UPoly{K}(K[c])) for c in D.c])
    Bz = UPoly{Kz}(Kz[frac(UPoly{K}(K[ai(k), -di(k)])) for k in 1:n])
    r = resultant(Dz, Bz)
    iszero(r) && throw(RischError("zero resultant in the residue computation"))
    isone(r.den) || throw(RischError("residue polynomial is not a polynomial"))
    Rz = r.num
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
    if CT === Q && degree(rest) == 2                   # a conjugate pair in ℚ(√d) (Stage 5b)
        qt = tower_quad_terms(T, i, A, D, dD, rest)
        if qt !== nothing
            append!(out, qt[1])
            append!(quads, qt[2])
            rest = one(rest)
        end
    elseif CT === QI && degree(rest) == 2              # a pair α ± β√d over ℚ(i) (Step 7)
        qt = ext_quad_terms(T, i, A, D, dD, rest)
        if qt !== nothing
            push!(quads, qt)
            rest = one(rest)
        end
    end
    degree(rest) > 0 && throw(RischNotImplemented(
        "the residues are algebraic constants of degree > 2 (or a quadratic pair over a constant " *
        "field other than ℚ); general algebraic constants / RootSum are not implemented"))
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
        (isempty(r.atans) && isempty(r.quads)) || throw(RischNotImplemented(
            "an atan (or quadratic-irrational log) term would multiply a power of the logarithm"))
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
        isempty(res.unresolved) || throw(RischNotImplemented(
            "the logarithmic part has irrational residues; algebraic constants are planned for Stage 5"))
        return ElemIntegral(res.rational,
                            Tuple{ctype(T),Any}[(c, frac(w)) for (c, w) in res.logs],
                            Tuple{ctype(T),Any}[(c, u) for (c, u) in res.atans],
                            Any[tower_quad(q) for q in res.quads])
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
        rl, rq = residue_logs(T, i, R, Dsf)
        for (c, W) in rl
            push!(logs, (c, frac(W)))
            corr += c * degree(W)
        end
        for q in rq                                     # 5b ratio terms: degree 0, no correction
            q isa ExtQuadPair && (corr += ext_corr(q))
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
            y === nothing && throw(NotElementary(
                "the Risch differential equation y' + $j·u'·y = a has no solution in the coefficient field, " *
                "so the coefficient of exp(u)^$j has no elementary integral"))
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
    i == 0 && return cconj(f)
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

# Re(c log w) as real pieces (coefficient, :log | :atan, argument), see the header above
function real_log_pieces(T::Tower, kinds, c, w)
    C = ctype(T)
    j = levelof(T, w)
    sw = tconj(T, kinds, w, j)
    sc = cconj(c)
    half = inv(cfromQ(C, Q(2)))
    I = cimag(C)
    cr = (c + sc) * half
    ci = (c - sc) * inv(I + I)
    pieces = Tuple{Any,Symbol,Any}[]
    if sw == w
        iszero(cr) || push!(pieces, (cr, :log, w))
        return pieces
    end
    iszero(cr) || push!(pieces, (cr * half, :log, w * sw))
    U = (w + sw) * lconst(T, half, j)
    V = (w - sw) * lconst(T, inv(I + I), j)
    (iszero(ci) || iszero(U) || iszero(V)) || push!(pieces, (-ci, :atan, V / U))  # U = 0: w/σw = -1, constant
    pieces
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
        for (coef, kind, arg) in pieces
            a = liftto(TT, arg, L)
            da = kind === :log ? D(TT, L, a) / a : D(TT, L, a) / (one(a) + a * a)
            ds = ds + lconst(TT, coef, L) * da
            t = mk(b, kind, real_term(b, TT, kk, arg))
            push!(ts, isone(coef) ? t : mk(b, :*, cterm(b, coef), t))
        end
        ds
    end
    for (c, w) in res.logs
        tot = tot + emit!(T, kinds, real_log_pieces(T, kinds, c, w))
    end
    isempty(res.atans) || throw(RischError("unexpected atan terms over ℚ(i)"))
    for q in res.quads
        q isa ExtQuadPair || throw(RischError("unexpected term $(typeof(q)) over ℚ(i)"))
        T2 = q.T2
        k2 = sigma_kinds(T2)
        a2, W2 = galois_d(q.a), change_constants(T2, T2, q.W, galois_d)
        ds = emit!(T2, k2, real_log_pieces(T2, k2, q.a, q.W)) +
             emit!(T2, k2, real_log_pieces(T2, k2, a2, W2))
        tot = tot + change_constants(T2, T, ds, qs_down)
    end
    tot == liftto(T, f, L) ||
        throw(RischError("internal check failed: the real form of the antiderivative does not differentiate back"))
    isempty(ts) && return b.lift(0)
    length(ts) == 1 ? ts[1] : mk(b, :+, ts...)
end

# ---------------------------------------------------------------------------
# Public API
# ---------------------------------------------------------------------------
function risch_integrate(f, x; build = nothing, lift = nothing, verify::Bool = true)
    if has_trig(f)                     # polynomial × exp × trig first (Stage 5c), else the ℚ(i) tower
        try
            return integrate_trig(f, x; build = build, lift = lift, verify = verify)
        catch e
            e isa RischNotImplemented || rethrow()
        end
    end
    T, el = build_tower(f, string(x))
    L = length(T.levels)
    bd = Builder(build === nothing ? auto_build(f, x) : build,
                 lift === nothing ? auto_lift(f, x) : lift, x, T.consts)
    if is_complex_field(ctype(T))      # Step 7: integrate over ℚ(i), then take the real part
        res = integrate_el(T, L, el)
        verify && !check_tower(T, L, res, el) &&
            throw(RischError("internal check failed: derivative of the result differs from the integrand"))
        return to_term_real(bd, T, L, res, el)
    end
    if L > 0
        res = integrate_el(T, L, el)
        verify && !check_tower(T, L, res, el) &&
            throw(RischError("internal check failed: derivative of the result differs from the integrand"))
        return to_term(bd, T, res)
    end
    F = el                              # an element of K_0 = C(x)
    res = integrate_rational(F)
    if !isempty(res.unresolved)
        rest = res.unresolved[1][1]
        throw(RischNotImplemented(
            "the logarithmic part has irrational residues (roots of $(rest.c) in z, low->high); " *
            "algebraic constants / RootSum are planned for Stage 5"))
    end
    verify && !check_result(res, F) &&
        throw(RischError("internal check failed: derivative of the result differs from the integrand"))
    to_term(bd, res)
end

end # module
