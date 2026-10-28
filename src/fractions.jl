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
# Henrici's algorithms (step PF): gcds of the factors instead of the products; the result is the same
# normal form (coprime, monic denominator) as `frac` of the product, so equality is unaffected
function Base.:+(f::Frac{P}, g::Frac{P}) where {P}
    iszero(f) && return g
    iszero(g) && return f
    a, b, c, d = f.num, f.den, g.num, g.den
    isone(b) && isone(d) && return Frac{P}(a + c, b)       # both polynomials
    b == d && return frac(a + c, b)
    isone(b) && return Frac{P}(a * d + c, d)               # coprime already
    isone(d) && return Frac{P}(a + c * b, b)
    G = gcd(b, d)
    if degree(G) <= 0                                       # coprime denominators: reduced
        return Frac{P}(a * d + c * b, b * d)
    end
    bg, dg = quo(b, G), quo(d, G)
    t = a * dg + c * bg
    iszero(t) && return zero(f)
    h = gcd(t, G)
    degree(h) <= 0 ? Frac{P}(t, bg * d) : Frac{P}(quo(t, h), bg * quo(d, h))
end
Base.:-(f::Frac{P}, g::Frac{P}) where {P} = f + (-g)

# gcd over a rational function field K = B(t₁, …, tₖ) (parameters, tower monomials; B = ℚ, ℚ(i), ℚ(√d), …):
# first the images at a point tⱼ = vⱼ. When every coefficient is defined there and neither leading coefficient
# vanishes, a common factor of degree ≥ 1 keeps its degree in the images (Gauss: it divides the primitive parts),
# so coprime images mean coprime a, b, the usual case, without Euclid over K (each of whose steps
# normalises fractions by gcds one level down). Otherwise Euclid.
function Base.gcd(a::UPoly{T}, b::UPoly{T}) where {T<:Frac}
    degree(a) > 0 && degree(b) > 0 && coprime_image(a, b) && return one(a)
    euclid_gcd(a, b)
end
fbase(::Type{Frac{UPoly{S}}}) where {S} = fbase(S)
fbase(::Type{S}) where {S} = S
fdepth(::Type{Frac{UPoly{S}}}) where {S} = 1 + fdepth(S)
fdepth(::Type) = 0
# point k = 0, 1, …: tⱼ ↦ -3/7, 5/10, -7/13, … (k = 0), shifted by k/11 for the others
image_point(B, j::Int, k::Int = 0) = cfromQ(B, Q(isodd(j) ? -(2j + 1) : 2j + 1, 3j + 4) + Q(k, 11))
cimage(c, k::Int = 0) = c
function cimage(c::Frac{UPoly{S}}, k::Int = 0) where {S}
    n, d = pimage(c.num, k), pimage(c.den, k)
    (n === nothing || d === nothing || iszero(d)) ? nothing : n / d
end
function pimage(p::UPoly{S}, k::Int = 0) where {S}
    v = image_point(fbase(S), fdepth(S) + 1, k)
    r = zero(v)
    for i in length(p.c):-1:1
        ci = cimage(p.c[i], k)
        ci === nothing && return nothing
        r = r * v + ci
    end
    r
end
function coprime_image(a::UPoly{T}, b::UPoly{T}) where {T<:Frac}
    B = fbase(T)
    applicable(cfromQ, B, Q(1)) || return false
    im_(p) = (cs = map(cimage, p.c); (any(isnothing, cs) || iszero(cs[end])) ? nothing : UPoly{B}(B[c for c in cs]))
    ia = im_(a)
    ia === nothing && return false
    ib = im_(b)
    ib === nothing && return false
    degree(euclid_gcd(ia, ib)) == 0
end
function Base.:*(f::Frac{P}, g::Frac{P}) where {P}
    (iszero(f) || iszero(g)) && return zero(f)
    a, b, c, d = f.num, f.den, g.num, g.den
    isone(b) && isone(d) && return Frac{P}(a * c, b)
    g1 = isone(d) ? one(P) : gcd(a, d)
    g2 = isone(b) ? one(P) : gcd(c, b)
    a1, d1 = degree(g1) > 0 ? (quo(a, g1), quo(d, g1)) : (a, d)
    c1, b1 = degree(g2) > 0 ? (quo(c, g2), quo(b, g2)) : (c, b)
    Frac{P}(a1 * c1, b1 * d1)                               # b1, d1 monic: the product is monic
end
function Base.inv(f::Frac{P}) where {P}
    iszero(f) && throw(DivideError())
    l = lc(f.num)                                           # coprime already: only make monic
    isone(l) ? Frac{P}(f.den, f.num) : Frac{P}(scale_div(f.den, l), scale_div(f.num, l))
end
Base.:/(f::Frac{P}, g::Frac{P}) where {P} = f * inv(g)
Base.:*(n::Integer, f::Frac{P}) where {P} = iszero(n) ? zero(f) : Frac{P}(n * f.num, f.den)
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

# Resultant over K = B(t₁, …, tₖ), fraction-free (step FR). Euclid over K normalises nested fractions by
# gcds at every step, and the coefficients swell. Instead: scale a, b so that every coefficient lies in the
# ring B[t₁, …, tₖ] (all nested denominators 1), run the subresultant PRS there (Cohen, Algorithm 3.3.7),
# whose divisions are exact, and divide by the scale factors once at the end.
function resultant(a::UPoly{T}, b::UPoly{T}) where {T<:Frac}
    (iszero(a) || iszero(b)) && return zero(T)
    ma, mb = integral_multiplier(T, a.c), integral_multiplier(T, b.c)
    r = ff_resultant(UPoly{T}(T[c * ma for c in a.c]), UPoly{T}(T[c * mb for c in b.c]))
    r / (ma^degree(b) * mb^degree(a))
end

# m ∈ K with every c·m in B[t₁, …, tₖ]: the lcm L of the denominators, then the same one level down for the
# coefficients of the numerators c·L
integral_multiplier(::Type{T}, cs) where {T} = one(T)
function integral_multiplier(::Type{Frac{P}}, cs) where {S,P<:UPoly{S}}
    L = reduce(plcm, [c.den for c in cs]; init = one(P))
    nums = [c.num * quo(L, c.den) for c in cs]
    M = integral_multiplier(S, S[a for n in nums for a in n.c])
    Frac{P}(scale(M, L), one(P))
end

# a / b for a, b ∈ B[t₁, …, tₖ] when b divides a
exdiv(a::T, b::T) where {T} = a / b
function exdiv(a::Frac{P}, b::Frac{P}) where {P}
    (isone(a.den) && isone(b.den)) || throw(RischError("exdiv: not a polynomial"))
    Frac{P}(exquo(a.num, b.num), one(P))
end
function exquo(a::UPoly{S}, b::UPoly{S}) where {S}
    db, lb = degree(b), lc(b)
    n = length(a.c) - length(b.c) + 1
    n <= 0 && (iszero(a) ? (return zero(a)) : throw(RischError("exquo: not divisible")))
    r = copy(a.c)
    q = fill(zero(S), n)
    for k in n:-1:1
        iszero(r[k + db]) && continue
        coef = exdiv(r[k + db], lb)
        q[k] = coef
        for j in 0:db
            r[k + j] -= coef * b.c[j + 1]
        end
    end
    all(iszero, r) || throw(RischError("exquo: not divisible"))
    UPoly{S}(q)
end

# lc(b)^(deg a - deg b + 1) a mod b, without divisions
function prem(a::UPoly{T}, b::UPoly{T}) where {T}
    db, lb = degree(b), lc(b)
    e = degree(a) - db + 1
    r = a
    while !iszero(r) && degree(r) >= db
        t = UPoly{T}([fill(zero(T), degree(r) - db); lc(r)])
        r = scale(lb, r) - t * b
        e -= 1
    end
    scale(lb^e, r)
end

# the resultant over an integral domain by the subresultant PRS (Cohen, Algorithm 3.3.7, without contents)
function ff_resultant(a::UPoly{T}, b::UPoly{T}) where {T}
    (iszero(a) || iszero(b)) && return zero(T)
    s = 1
    if degree(a) < degree(b)
        a, b = b, a
        isodd(degree(a)) && isodd(degree(b)) && (s = -s)
    end
    degree(b) == 0 && return lc(b)^degree(a)
    g = h = one(T)
    while degree(b) > 0
        δ = degree(a) - degree(b)
        isodd(degree(a)) && isodd(degree(b)) && (s = -s)
        r = prem(a, b)
        iszero(r) && return zero(T)
        a, d = b, g * h^δ
        b = UPoly{T}(T[exdiv(c, d) for c in r.c])
        g = lc(a)
        h = δ == 0 ? h : exdiv(g^δ, h^(δ - 1))
    end
    da = degree(a)
    r = exdiv(lc(b)^da, h^(da - 1))
    s == 1 ? r : -r
end
