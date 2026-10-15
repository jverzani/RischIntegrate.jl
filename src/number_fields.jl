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
