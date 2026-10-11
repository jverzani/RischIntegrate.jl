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
function Base.inv(a::QI)
    n = a.re^2 + a.im^2
    QI(a.re / n, -a.im / n)
end
Base.:/(a::QI, b::QI) = a * inv(b)
toQI(p::UPoly{Q}) = UPoly{QI}(QI[QI(c, Q(0)) for c in p.c])

# ---------------------------------------------------------------------------
# Differential structure of ℚ(x): d/dx
# ---------------------------------------------------------------------------
const QX = UPoly{Q}
const QXF = Frac{UPoly{Q}}

dx(p::QX) = deriv(p)
dx(f::QXF) = frac(deriv(f.num) * f.den - f.num * deriv(f.den), f.den * f.den)
kconst(c::Q) = frac(QX(Q[c]))

function integrate_poly(p::QX)
    iszero(p) && return p
    QX(Q[i == 1 ? Q(0) : p.c[i - 1] / (i - 1) for i in 1:(length(p.c) + 1)])
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
            C = quo(R - B * Dstar * dV, V)
            g = g + frac(-B, j * V^j)
            R = C + divint(δ(B), j)
            D = quo(D, V)
        end
    end
    g, Qp, R, D
end

# ---------------------------------------------------------------------------
# Rothstein–Trager log part for R/D, D squarefree monic, deg R < deg D, over ℚ
# ---------------------------------------------------------------------------
struct RationalIntegral
    rational::QXF                          # rational (non-log) part
    logs::Vector{Tuple{Q,QX}}              # c * log(w)
    atans::Vector{Tuple{Q,QXF}}            # c * atan(u)
    unresolved::Vector{Any}                # (residue polynomial, R, D) not handled yet
end

function log_part(A::QX, D::QX)
    logs = Tuple{Q,QX}[]
    atans = Tuple{Q,QXF}[]
    unresolved = Any[]
    iszero(A) && return logs, atans, unresolved
    dD = deriv(D)
    # R(z) = res_x(D, A - z D') computed in the field ℚ(z)
    Kz = QXF
    n = max(length(A.c), length(dD.c))
    ai(i) = i <= length(A.c) ? A.c[i] : Q(0)
    di(i) = i <= length(dD.c) ? dD.c[i] : Q(0)
    Dz = UPoly{Kz}(Kz[kconst(c) for c in D.c])
    Bz = UPoly{Kz}(Kz[frac(QX(Q[ai(i), -di(i)])) for i in 1:n])
    r = resultant(Dz, Bz)
    iszero(r) && throw(RischError("zero resultant in the residue computation"))
    isone(r.den) || throw(RischError("residue polynomial is not a polynomial"))
    Rz = r.num
    degree(Rz) <= 0 && return logs, atans, unresolved
    Rsf = quo(Rz, gcd(Rz, deriv(Rz)))        # distinct residues
    roots = rational_roots(Rsf)
    rest = Rsf
    for a in roots
        W = gcd(D, A - scale(a, dD))
        degree(W) > 0 && push!(logs, (a, W))
        rest = quo(rest, QX(Q[-a, Q(1)]))
    end
    degree(rest) == 0 && return logs, atans, unresolved
    handled = false
    if degree(rest) == 2
        rest = monic(rest)
        p0, p1 = rest.c[1], rest.c[2]
        α = -p1 / 2
        s = rat_sqrt(-(p1^2 - 4 * p0))      # sqrt(-discriminant), only if rational
        if s !== nothing && !iszero(s)
            β = s / 2
            a = QI(α, β)
            W = gcd(toQI(D), toQI(A) - scale(a, toQI(dD)))
            U = QX(Q[w.re for w in W.c])
            V = QX(Q[w.im for w in W.c])
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
    end
    handled || push!(unresolved, (rest, A, D))
    logs, atans, unresolved
end

function integrate_rational(f::QXF)
    iszero(f) && return RationalIntegral(zero(QXF), Tuple{Q,QX}[], Tuple{Q,QXF}[], Any[])
    g, Qp, R, Dsf = hermite_reduce(dx, f.num, f.den)
    rational = g + frac(integrate_poly(Qp))
    logs, atans, unresolved = log_part(R, Dsf)
    RationalIntegral(rational, logs, atans, unresolved)
end

# d/dx of the computed antiderivative, in ℚ(x) (for self-verification)
function derivative_of(res::RationalIntegral)
    tot = dx(res.rational)
    for (c, w) in res.logs
        tot = tot + kconst(c) * frac(deriv(w), w)
    end
    for (c, u) in res.atans
        tot = tot + kconst(c) * dx(u) / (one(QXF) + u * u)
    end
    tot
end
check_result(res::RationalIntegral, f::QXF) = isempty(res.unresolved) && derivative_of(res) == f

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
function const_int(f::QXF)
    (isone(f.den) && degree(f.num) <= 0) || return nothing
    c = isempty(f.num.c) ? Q(0) : f.num.c[1]
    isone(denominator(c)) ? Int(numerator(c)) : nothing
end

const NONRATIONAL = (:exp, :log, :sin, :cos, :tan, :atan, :sinh, :cosh, :tanh, :abs, :sqrt, :cbrt)

function parse_rational(t, xk::String)::QXF
    if safe_iscall(t)
        args = arguments(t)
        if !isempty(args)
            n = opname(operation(t))
            n in NONRATIONAL && throw(RischNotImplemented(
                "`$n` is not a rational function; integrands with exp/log towers " *
                "are planned for Stage 2/3 (see the roadmap in Risch.jl)"))
            a = QXF[parse_rational(u, xk) for u in args]
            if n === :+
                return foldl(+, a; init = zero(QXF))
            elseif n === :-
                return length(a) == 1 ? -a[1] : a[1] - foldl(+, a[2:end]; init = zero(QXF))
            elseif n === :*
                return foldl(*, a; init = one(QXF))
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

struct Builder
    build::Any
    lift::Any
    x::Any
end
const OPS = Dict{Symbol,Function}(:+ => +, :* => *, :/ => /, :^ => ^, :exp => exp,
                                  :log => log, :atan => atan)
mk(b::Builder, name::Symbol, args...) = b.build(OPS[name], args...)

default_build(op, args...) = op(args...)

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

function poly_term(b::Builder, p::QX)
    iszero(p) && return b.lift(0)
    ts = Any[]
    for (i, c) in enumerate(p.c)
        iszero(c) && continue
        k = i - 1
        if k == 0
            push!(ts, b.lift(num(c)))
        else
            xk = k == 1 ? b.x : mk(b, :^, b.x, b.lift(k))
            push!(ts, isone(c) ? xk : mk(b, :*, b.lift(num(c)), xk))
        end
    end
    length(ts) == 1 ? ts[1] : mk(b, :+, ts...)
end
frac_term(b::Builder, f::QXF) =
    isone(f.den) ? poly_term(b, f.num) : mk(b, :/, poly_term(b, f.num), poly_term(b, f.den))

function to_term(b::Builder, res::RationalIntegral)
    ts = Any[]
    iszero(res.rational) || push!(ts, frac_term(b, res.rational))
    for (c, w) in res.logs
        l = mk(b, :log, poly_term(b, w))
        push!(ts, isone(c) ? l : mk(b, :*, b.lift(num(c)), l))
    end
    for (c, u) in res.atans
        l = mk(b, :atan, frac_term(b, u))
        push!(ts, isone(c) ? l : mk(b, :*, b.lift(num(c)), l))
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

mutable struct Tower
    xk::String
    levels::Vector{Level}
    Ts::Vector{DataType}      # Ts[i+1] is the type of Kᵢ
    scales::Dict{Int,Int}     # exp-generator refinement hints (see Restart)
    nexp::Int
end
Tower(xk::String, scales::Dict{Int,Int}) = Tower(xk, Level[], DataType[QXF], scales, 0)

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
lq(T::Tower, c::Q, j::Int) = liftto(T, kconst(c), j)

# constant value (∈ ℚ) of a tower element, or nothing
const_value(f::QXF) = (isone(f.den) && degree(f.num) <= 0) ? (isempty(f.num.c) ? Q(0) : f.num.c[1]) : nothing
function const_value(f::Frac{UPoly{K}}) where {K}
    (isone(f.den) && degree(f.num) <= 0) || return nothing
    isempty(f.num.c) ? Q(0) : const_value(f.num.c[1])
end

# --- the derivation on every level -------------------------------------------
D(T::Tower, i::Int, f::QXF) = dx(f)
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

# --- ℚ-linear dependence between field elements -------------------------------
plcm(a::P, b::P) where {P<:UPoly} = quo(a * b, gcd(a, b))

# coordinate vectors over ℚ of elements of one field: linear relations among the
# elements correspond exactly to linear relations among the vectors
function flat(elems::Vector{QXF})
    L = reduce(plcm, [e.den for e in elems]; init = one(QX))
    nums = [e.num * quo(L, e.den) for e in elems]
    m = maximum(length(n.c) for n in nums)
    [Q[k <= length(n.c) ? n.c[k] : Q(0) for k in 1:m] for n in nums]
end
function flat(elems::Vector{Frac{UPoly{K}}}) where {K}
    L = reduce(plcm, [e.den for e in elems]; init = one(UPoly{K}))
    nums = [e.num * quo(L, e.den) for e in elems]
    m = maximum(length(n.c) for n in nums)
    parts = [flat(K[k <= length(n.c) ? n.c[k] : zero(K) for n in nums]) for k in 1:m]
    [reduce(vcat, (parts[k][j] for k in 1:m); init = Q[]) for j in eachindex(elems)]
end

# solve  Σ r_j cols[j] = t  over ℚ (nothing if inconsistent)
function solve_columns(cols::Vector{Vector{Q}}, t::Vector{Q})
    m, k = length(t), length(cols)
    M = Q[j <= k ? cols[j][i] : t[i] for i in 1:m, j in 1:(k + 1)]
    piv = Int[]
    row = 1
    for col in 1:k
        row > m && break
        p = findfirst(i -> !iszero(M[i, col]), row:m)
        p === nothing && continue
        p += row - 1
        if p != row
            M[row, :], M[p, :] = M[p, :], M[row, :]
        end
        M[row, :] = M[row, :] / M[row, col]
        for i in 1:m
            i != row && !iszero(M[i, col]) && (M[i, :] = M[i, :] - M[i, col] * M[row, :])
        end
        push!(piv, col)
        row += 1
    end
    for i in row:m
        iszero(M[i, k + 1]) || return nothing
    end
    sol = fill(Q(0), k)
    for (i, col) in enumerate(piv)
        sol[col] = M[i, k + 1]
    end
    sol
end

function solve_relation(target::F, basis::Vector{F}) where {F}
    isempty(basis) && return iszero(target) ? Q[] : nothing
    vs = flat(F[basis; target])
    solve_columns(vs[1:(end - 1)], vs[end])
end

function add_level!(T::Tower, kind::Symbol, arg, dtheta, seq::Int)
    K = T.Ts[end]
    push!(T.levels, Level(kind, arg, dtheta, seq))
    push!(T.Ts, Frac{UPoly{K}})
    nothing
end

# --- exp and log of tower elements --------------------------------------------
function make_exp(T::Tower, u)
    c = const_value(u)
    if c !== nothing
        iszero(c) && return one(QXF)
        throw(RischNotImplemented("exp of the nonzero constant $c involves the transcendental " *
                                  "constant e^$c (constant-field extensions are planned for Stage 5)"))
    end
    top = length(T.levels)
    u = liftto(T, u, top)
    K = T.Ts[end]
    basis = K[]
    for (i, lv) in enumerate(T.levels)
        push!(basis, lv.kind === :exp ? liftto(T, lv.arg, top) : liftto(T, theta(T, i), top))
    end
    push!(basis, one(K))
    r = solve_relation(u, basis)
    if r !== nothing
        iszero(r[end]) || throw(RischNotImplemented(
            "exp(u + c) with a nonzero constant c needs the transcendental constant e^c (Stage 5)"))
        res = one(K)
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
    c = const_value(u)
    if c !== nothing
        isone(c) && return zero(QXF)
        throw(RischNotImplemented("log of the constant $c is a new transcendental constant " *
                                  "(constant-field extensions are planned for Stage 5)"))
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
    r = solve_relation(w, basis)
    if r !== nothing
        # u^q = c * prod(...)  with c a constant; log u = sum r_i * (log of generator i) + log c / q
        q = reduce(lcm, denominator.(r); init = big(1))
        R = u^Int(q)
        res = zero(QXF)
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
        cv = const_value(R)
        cv === nothing && throw(RischError("inconsistent logarithmic relation (not a constant ratio)"))
        abs(cv) == 1 || throw(RischNotImplemented(
            "log(u) = (combination of generators) + log($(abs(cv)))/$q: a new constant (Stage 5)"))
        return liftto(T, res, top)
    end
    add_level!(T, :log, u, UPoly{K}(K[w]), 0)
    theta(T, top + 1)
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
            n in TRIG && throw(RischNotImplemented(
                "`$n` is not supported yet: trigonometric input needs complex (ℚ(i)) " *
                "coefficients and real-form output (Stage 5)"))
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
                k = const_value(ex)
                if k !== nothing
                    isone(denominator(k)) && abs(k) <= 10_000 && return base^Int(numerator(k))
                    throw(RischNotImplemented("rational power $k is an algebraic (radical) function"))
                end
                lg = make_log(T, base)
                p, m = unify(T, ex, lg)
                return make_exp(T, p * m)
            else
                throw(RischNotImplemented("unsupported operation `$n`"))
            end
        end
    end
    string(t) == T.xk && return frac(xpoly(Q))
    is_e_const(t) && throw(RischNotImplemented(
        "the constant e is transcendental; constant-field extensions are planned for Stage 5"))
    r = leaf_rational(t)
    r !== nothing && return kconst(r)
    throw(RischNotImplemented("symbol `$t` is not the integration variable; " *
                              "symbolic parameters are not supported yet"))
end

# Build the tower for `f`. A Restart (a rational multiple such as exp(x/2) after
# exp(x)) refines the generator and re-parses; the hints only ever grow.
function build_tower(f, xk::String)
    scales = Dict{Int,Int}()
    for _ in 1:50
        T = Tower(xk, scales)
        try
            el = parse_tower(f, T)
            return minimal(T, el)
        catch e
            e isa Restart || rethrow()
            scales[e.seq] = lcm(get(scales, e.seq, 1), e.q)
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
    b = Builder(build === nothing ? default_build : build,
                lift === nothing ? auto_lift(f, x) : lift, x)
    tower_to_term(b, T, d)
end

# ---------------------------------------------------------------------------
# Stage 4: the Risch differential equation  y' + f y = g  over ℚ(x)
#
# Used for  ∫ a θ^j  with θ = exp(u):  y' + (j u') y = a  (Bronstein ch. 6).
# Since f = j u' is a derivative it has no simple poles, which makes the bounds
# below sound (valuations at a finite place p, with f ~ p^-m, g ~ p^-k):
#   * m >= 2 : f y dominates y', so v(y) = v(g) + m: a pole of order k - m at most;
#   * f regular at p : y' dominates when y has a pole, so v(y) = v(g) + 1: order k - 1.
#   Hence y = N/D with D built from the poles of g only.
# At infinity (a = deg f, γ = deg g): a >= 0 gives deg y = γ - a, a <= -2 gives
# deg y <= max(γ + 1, 0). The numerator N is then a polynomial of known degree
# bound, found by exact linear algebra over ℚ (the solution is unique because the
# homogeneous solution exp(-∫f) is not rational).
# Returns y ∈ ℚ(x), or `nothing` if there is no rational solution.
# ---------------------------------------------------------------------------
function rde_base(f::QXF, g::QXF)
    iszero(g) && return zero(QXF)
    iszero(f) && throw(RischError("RDE with f = 0 is plain integration"))
    Fn, Df = f.num, f.den
    G, Dg = g.num, g.den
    a = degree(Fn) - degree(Df)
    a == -1 && throw(RischNotImplemented("RDE with a simple pole of f at infinity"))
    # denominator bound
    Dn = one(QX)
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
    mono(k) = QX(vcat(fill(Q(0), k), [Q(1)]))
    cols = QX[]
    for k in 0:M
        N = mono(k)
        dN = k == 0 ? zero(QX) : k * mono(k - 1)
        push!(cols, Df * Dg * (Dn * dN - dD * N) + Fn * Dg * Dn * N)
    end
    target = G * Df * Dn * Dn
    len = maximum(length(p.c) for p in [cols; target])
    coords(p) = Q[i <= length(p.c) ? p.c[i] : Q(0) for i in 1:len]
    sol = solve_columns([coords(p) for p in cols], coords(target))
    sol === nothing && return nothing
    y = frac(QX(sol), Dn)
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
    (r === nothing || !isempty(r.logs) || !isempty(r.atans)) ? nothing : r.v
end

function rde(T::Tower, m::Int, f, g)
    iszero(g) && return zero(T.Ts[m + 1])
    m == 0 && return rde_base(f, g)
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
struct ElemIntegral
    v::Any                              # rational part, element of Kᵢ
    logs::Vector{Tuple{Q,Any}}          # (c, w):  c * log(w)
    atans::Vector{Tuple{Q,Any}}         # (c, u):  c * atan(u), u ∈ ℚ(x) (base level only)
end

# R(z) = res_θ(D, A - z δD) must have constant roots; returns [(c, gcd(D, A - c δD))]
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
    out = Tuple{Q,Any}[]
    degree(Rz) <= 0 && return out
    Rm = monic(Rz)
    qc = Q[]
    for c in Rm.c
        v = const_value(c)
        v === nothing && throw(NotElementary(
            "the residues of the integrand are not constants (residue criterion)"))
        push!(qc, v)
    end
    Rq = QX(qc)
    Rsf = quo(Rq, gcd(Rq, deriv(Rq)))
    rest = Rsf
    for a in rational_roots(Rsf)
        W = gcd(D, A - scale(lq(T, a, i - 1), dD))
        degree(W) > 0 && push!(out, (a, W))
        rest = quo(rest, QX(Q[-a, Q(1)]))
    end
    degree(rest) > 0 && throw(RischNotImplemented(
        "the residues are irrational or complex constants; algebraic constants are planned for Stage 5"))
    out
end

# ∫ p, p ∈ K[θ], θ = log(u): returns (q ∈ K[θ], logs (c, w ∈ K), atans) with Dq + Σ c w'/w = p
function integrate_log_poly(T::Tower, i::Int, p::UPoly)
    K = T.Ts[i]
    P = UPoly{K}
    Lθ = T.levels[i].dtheta.c[1]                       # u'/u
    q = zero(P)
    while degree(p) > 0
        n = degree(p)
        r = integrate_el(T, i - 1, lc(p))
        isempty(r.atans) || throw(RischNotImplemented(
            "an atan term would multiply a power of the logarithm (needs complex constants, Stage 5)"))
        tgt = zero(K)                                   # Σ cⱼ wⱼ'/wⱼ, must equal c·u'/u
        for (cj, wj) in r.logs
            tgt = tgt + lq(T, cj, i - 1) * (D(T, i - 1, wj) / wj)
        end
        c = Q(0)
        if !iszero(tgt)
            sol = solve_relation(tgt, K[Lθ])
            sol === nothing && throw(NotElementary(
                "the integral of the coefficient of log^$n involves logarithms other than log(u)"))
            c = sol[1]
        end
        coeffs = fill(zero(K), n + 2)
        coeffs[n + 2] = lq(T, c / (n + 1), i - 1)
        coeffs[n + 1] = r.v
        qn = P(coeffs)
        q = q + qn
        p = p - Dp(T, i, qn)
        degree(p) < n || throw(RischError("polynomial reduction did not lower the degree"))
    end
    logs = Tuple{Q,Any}[]
    atans = Tuple{Q,Any}[]
    if !iszero(p)
        r0 = integrate_el(T, i - 1, p.c[1])
        q = q + P(K[r0.v])
        append!(logs, r0.logs)
        append!(atans, r0.atans)
    end
    q, logs, atans
end

function integrate_el(T::Tower, i::Int, f)::ElemIntegral
    if i == 0
        res = integrate_rational(f)
        isempty(res.unresolved) || throw(RischNotImplemented(
            "the logarithmic part has irrational residues; algebraic constants are planned for Stage 5"))
        return ElemIntegral(res.rational,
                            Tuple{Q,Any}[(c, frac(w)) for (c, w) in res.logs],
                            Tuple{Q,Any}[(c, u) for (c, u) in res.atans])
    end
    lv = T.levels[i]
    K = T.Ts[i]
    P = UPoly{K}
    F = T.Ts[i + 1]
    iszero(f) && return ElemIntegral(zero(F), Tuple{Q,Any}[], Tuple{Q,Any}[])
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
    logs = Tuple{Q,Any}[]
    atans = Tuple{Q,Any}[]
    corr = Q(0)
    if !iszero(R)
        for (c, W) in residue_logs(T, i, R, Dsf)
            push!(logs, (c, frac(W)))
            corr += c * degree(W)
        end
    end
    v = g
    if lv.kind === :log
        maxj = maximum(keys(laurent); init = 0)
        p = P(K[get(laurent, j, zero(K)) for j in 0:maxj])
        q, lp, ap = integrate_log_poly(T, i, p)
        v = v + frac(q)
        for (c, w) in lp
            push!(logs, (c, frac(P(K[w]))))
        end
        append!(atans, ap)
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
        end
        iszero(corr) || (v = v - lq(T, corr, i) * liftto(T, lv.arg, i))
    end
    ElemIntegral(v, logs, atans)
end

# d/dx of the antiderivative, computed in the tower, must equal the integrand
function check_tower(T::Tower, L::Int, res::ElemIntegral, f)
    tot = D(T, L, liftto(T, res.v, L))
    for (c, w) in res.logs
        w = liftto(T, w, L)
        tot = tot + lq(T, c, L) * (D(T, L, w) / w)
    end
    for (c, u) in res.atans
        du = liftto(T, dx(u) / (one(QXF) + u * u), L)
        tot = tot + lq(T, c, L) * du
    end
    tot == f
end

function to_term(b::Builder, T::Tower, res::ElemIntegral)
    ts = Any[]
    iszero(res.v) || push!(ts, tower_to_term(b, T, res.v))
    for (c, w) in res.logs
        l = mk(b, :log, tower_to_term(b, T, w))
        push!(ts, isone(c) ? l : mk(b, :*, b.lift(num(c)), l))
    end
    for (c, u) in res.atans
        l = mk(b, :atan, frac_term(b, u))
        push!(ts, isone(c) ? l : mk(b, :*, b.lift(num(c)), l))
    end
    isempty(ts) && return b.lift(0)
    length(ts) == 1 ? ts[1] : mk(b, :+, ts...)
end

# ---------------------------------------------------------------------------
# Public API
# ---------------------------------------------------------------------------
function risch_integrate(f, x; build = nothing, lift = nothing, verify::Bool = true)
    T, el = build_tower(f, string(x))
    L = length(T.levels)
    bd = Builder(build === nothing ? default_build : build,
                 lift === nothing ? auto_lift(f, x) : lift, x)
    if L > 0
        res = integrate_el(T, L, el)
        verify && !check_tower(T, L, res, el) &&
            throw(RischError("internal check failed: derivative of the result differs from the integrand"))
        return to_term(bd, T, res)
    end
    F = el::QXF
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
