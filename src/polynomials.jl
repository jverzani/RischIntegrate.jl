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
    z = zero(T)
    r = fill(z, length(p.c) + length(q.c) - 1)
    for i in eachindex(p.c)
        a = p.c[i]
        iszero(a) && continue                   # (nested coefficients are mostly zero)
        for j in eachindex(q.c)
            b = q.c[j]
            iszero(b) && continue
            r[i + j - 1] += a * b
        end
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

scale(a::T, p::UPoly{T}) where {T} = UPoly{T}(T[iszero(c) ? c : a * c for c in p.c])
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
Base.gcd(a::UPoly{T}, b::UPoly{T}) where {T} = euclid_gcd(a, b)
function euclid_gcd(a::UPoly{T}, b::UPoly{T}) where {T}
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
