# ---------------------------------------------------------------------------
# One type for the constant field ℚ(t₁, …, tₖ) (or ℚ(i)(t₁, …, tₖ)): CF{B}
#
# The nested representation `cfield(k) = Frac{UPoly{cfield(k - 1)}}` makes every parameter count a type of its own,
# and the integrator compiles again for each (sample 620, nine parameters: 2385 specializations, 326 s of compilation
# on a first call). CF{B} keeps the same recursive representation but holds the depth as a field:
#   lev = 0:  a number of B (ℚ or ℚ(i)), in `val`;
#   lev = j:  a rational function in tⱼ, `f`, whose coefficients are CF{B} of level < j.
# Canonical form: lev is the highest generator that occurs (a value constant in tⱼ is stored as its coefficient), and
# `f` is in `Frac`'s normal form (coprime, monic denominator), so structural equality is equality. A value of a lower
# level acts as a constant coefficient at any level, which makes `zero(CF{B})`, `one(CF{B})` level-free, as the
# generic polynomial code needs. Arithmetic at level L is the existing `Frac`/`UPoly` code over CF{B}, with the gcds
# of `fractions.jl` (images at points, subresultant PRS) through the CF methods of `cimage`, `integral_multiplier`,
# `exdiv` and `nleaves` below.
# (Stage 1: the type and its arithmetic, tested against the nested types; not yet the constant field of a tower.)
# ---------------------------------------------------------------------------

struct CF{B}
    lev::Int
    val::B
    f::Union{Nothing,Frac{UPoly{CF{B}}}}
end

const CFFrac{B} = Frac{UPoly{CF{B}}}
CF{B}(v::B) where {B} = CF{B}(0, v, nothing)

# shared zeros and ones (`val` of a value of level ≥ 1 is unused, and zero(Rational{BigInt}) allocates BigInts each time:
# most of the time of a gcd over seven parameters went there)
const ZERO_Q, ONE_Q = zero(Q), one(Q)
const ZERO_QI, ONE_QI = zero(QI), one(QI)
bzero(::Type{Q}) = ZERO_Q
bzero(::Type{QI}) = ZERO_QI
bzero(::Type{B}) where {B} = zero(B)
bone(::Type{Q}) = ONE_Q
bone(::Type{QI}) = ONE_QI
bone(::Type{B}) where {B} = one(B)
const CF_ZERO_Q, CF_ONE_Q = CF{Q}(0, ZERO_Q, nothing), CF{Q}(0, ONE_Q, nothing)
const CF_ZERO_QI, CF_ONE_QI = CF{QI}(0, ZERO_QI, nothing), CF{QI}(0, ONE_QI, nothing)
Base.zero(::Type{CF{Q}}) = CF_ZERO_Q
Base.zero(::Type{CF{QI}}) = CF_ZERO_QI
Base.one(::Type{CF{Q}}) = CF_ONE_Q
Base.one(::Type{CF{QI}}) = CF_ONE_QI
Base.zero(::Type{CF{B}}) where {B} = CF{B}(bzero(B))
Base.one(::Type{CF{B}}) where {B} = CF{B}(bone(B))
Base.zero(c::CF) = zero(typeof(c))
Base.one(c::CF) = one(typeof(c))
Base.iszero(c::CF) = c.lev == 0 && iszero(c.val)
Base.isone(c::CF) = c.lev == 0 && isone(c.val)
Base.:(==)(a::CF{B}, b::CF{B}) where {B} = a.lev == b.lev && (a.lev == 0 ? a.val == b.val : a.f == b.f)
Base.hash(c::CF, h::UInt) = c.lev == 0 ? hash(c.val, hash(:CF0, h)) : hash(c.f, hash(c.lev, h))

cflevel(c::CF) = c.lev
# the generator tⱼ
cf_gen(::Type{CF{B}}, j::Int) where {B} = (j >= 1 || throw(ArgumentError("generator $j")); CF{B}(j, bzero(B), frac(xpoly(CF{B}))))
cfromQ(::Type{CF{B}}, q::Q) where {B} = CF{B}(cfromQ(B, q))

# c at level L ≥ c.lev, as an element of Frac{UPoly{CF}} in t_L
cf_at(c::CF{B}, L::Int) where {B} = c.lev == L ? c.f : CFFrac{B}(UPoly{CF{B}}(CF{B}[c]), one(UPoly{CF{B}}))
# the canonical CF of f ∈ Frac{UPoly{CF}} at level L: demoted to its coefficient when free of t_L
function cf_make(::Type{CF{B}}, L::Int, f::CFFrac{B}) where {B}
    (degree(f.num) <= 0 && degree(f.den) == 0) || return CF{B}(L, bzero(B), f)
    iszero(f.num) ? zero(CF{B}) : f.num.c[1]            # (den monic of degree 0: 1)
end

function cf_binop(op, a::CF{B}, b::CF{B}) where {B}
    a.lev == 0 && b.lev == 0 && return CF{B}(op(a.val, b.val))
    L = max(a.lev, b.lev)
    cf_make(CF{B}, L, op(cf_at(a, L), cf_at(b, L)))
end
function Base.:+(a::CF{B}, b::CF{B}) where {B}
    iszero(a) && return b
    iszero(b) && return a
    cf_binop(+, a, b)
end
Base.:-(a::CF{B}) where {B} = a.lev == 0 ? CF{B}(-a.val) : CF{B}(a.lev, bzero(B), -a.f)
Base.:-(a::CF{B}, b::CF{B}) where {B} = a + (-b)
function Base.:*(a::CF{B}, b::CF{B}) where {B}
    (iszero(a) || iszero(b)) && return zero(a)
    isone(a) && return b
    isone(b) && return a
    a.lev == 0 && b.lev == 0 && return CF{B}(a.val * b.val)
    # a lower-level factor scales the coefficients of the other's numerator (no gcds: it is a unit there)
    a.lev < b.lev && return CF{B}(b.lev, bzero(B), CFFrac{B}(scale(a, b.f.num), b.f.den))
    b.lev < a.lev && return CF{B}(a.lev, bzero(B), CFFrac{B}(scale(b, a.f.num), a.f.den))
    cf_make(CF{B}, a.lev, a.f * b.f)
end
function Base.inv(a::CF{B}) where {B}
    iszero(a) && throw(DivideError())
    a.lev == 0 ? CF{B}(inv(a.val)) : CF{B}(a.lev, bzero(B), inv(a.f))
end
Base.:/(a::CF{B}, b::CF{B}) where {B} = a * inv(b)
Base.:*(n::Integer, c::CF{B}) where {B} = iszero(n) ? zero(c) : c.lev == 0 ? CF{B}(n * c.val) : CF{B}(c.lev, bzero(B), n * c.f)
Base.:*(c::CF, n::Integer) = n * c
function Base.:^(c::CF, n::Integer)
    n < 0 && return inv(c)^(-n)
    r, b = one(c), c
    while n > 0
        isodd(n) && (r = r * b)
        n >>= 1
        n > 0 && (b = b * b)
    end
    r
end

# --- the gcd machinery of fractions.jl for coefficients CF (as for T<:Frac there) -----------------------------
nleaves(c::CF) = c.lev == 0 ? 1 : nleaves(c.f)
# the image at the point of `image_point` (tⱼ ↦ image_point(B, j, k)), or nothing where a denominator vanishes
function cimage(c::CF{B}, k::Int = 0) where {B}
    c.lev == 0 && return c.val
    v = image_point(B, c.lev, k)
    ev(p) = (r = zero(B); for i in length(p.c):-1:1; ci = cimage(p.c[i], k); ci === nothing && return nothing; r = r * v + ci; end; r)
    n, d = ev(c.f.num), ev(c.f.den)
    (n === nothing || d === nothing || iszero(d)) ? nothing : n / d
end
fbase(::Type{CF{B}}) where {B} = B
# m with every c·m a polynomial in t₁, …, tₖ: at the highest level L of the cs, the lcm of the denominators in t_L, then
# the same for the coefficients one level down (all coefficients of level < L, constants at L included)
function integral_multiplier(::Type{CF{B}}, cs) where {B}
    L = maximum((c.lev for c in cs); init = 0)
    L == 0 && return one(CF{B})
    P = UPoly{CF{B}}
    fs = [cf_at(c, L) for c in cs]
    D = reduce(plcm, [f.den for f in fs]; init = one(P))
    nums = [f.num * quo(D, f.den) for f in fs]
    M = integral_multiplier(CF{B}, CF{B}[a for n in nums for a in n.c])
    cf_make(CF{B}, L, CFFrac{B}(scale(M, D), one(P)))
end
# a / b for polynomials a, b in t₁, …, tₖ when b divides a
function exdiv(a::CF{B}, b::CF{B}) where {B}
    (a.lev == 0 && b.lev == 0) && return CF{B}(a.val / b.val)
    b.lev == 0 && return a / b                          # (a unit)
    L = max(a.lev, b.lev)
    fa, fb = cf_at(a, L), cf_at(b, L)
    (isone(fa.den) && isone(fb.den)) || throw(RischError("exdiv: not a polynomial"))
    cf_make(CF{B}, L, CFFrac{B}(exquo(fa.num, fb.num), one(UPoly{CF{B}})))
end
# polynomials whose coefficients are all numbers (level 0) as UPoly{B}: the nested types' innermost level, where Euclid
# over B is the whole gcd (through the image test it ran twice: squarefree over three parameters took twice as long)
cf_level0(p::UPoly{<:CF}) = all(c -> c.lev == 0, p.c)
to_bpoly(p::UPoly{CF{B}}) where {B} = UPoly{B}(B[c.val for c in p.c], Val(:fresh))
from_bpoly(::Type{CF{B}}, p::UPoly{B}) where {B} = UPoly{CF{B}}(CF{B}[CF{B}(c) for c in p.c], Val(:fresh))
function Base.gcd(a::UPoly{CF{B}}, b::UPoly{CF{B}}) where {B}
    (cf_level0(a) && cf_level0(b)) && return from_bpoly(CF{B}, euclid_gcd(to_bpoly(a), to_bpoly(b)))
    (degree(a) <= 0 || degree(b) <= 0) && return euclid_gcd(a, b)
    d = image_gcd_degree(a, b)
    d == 0 && return one(a)
    d === nothing || d == min(degree(a), degree(b)) ? euclid_gcd(a, b) : guarded_gcd(a, b)
end
function image_gcd_degree(a::UPoly{CF{B}}, b::UPoly{CF{B}}) where {B}
    im_(p) = (cs = map(cimage, p.c); (any(isnothing, cs) || iszero(cs[end])) ? nothing : UPoly{B}(B[c for c in cs]))
    ia = im_(a)
    ia === nothing && return nothing
    ib = im_(b)
    ib === nothing && return nothing
    degree(euclid_gcd(ia, ib))
end
# the size of guarded_gcd's test as the nested representation counts it: a value of level j inside level L padded with
# one constant wrapper per missing level (c ↦ c/1, the 1 at depth d with 2^d leaves). Counted with the CF's own, more compact sizes, the
# test switched to ff_gcd where the nested types stay with Euclid (squarefree over seven parameters: 68 s, not 0.4 s)
nleaves_at(c::CF, L::Int) = L == 0 ? 1 : c.lev < L ? nleaves_at(c, L - 1) + 2^(L - 1) :   # (+ the nested 1 at depth L - 1)
    sum((nleaves_at(x, L - 1) for x in c.f.num.c); init = 0) + sum((nleaves_at(x, L - 1) for x in c.f.den.c); init = 0)
function nleaves_nested(p::UPoly{<:CF})
    L = maximum((c.lev for c in p.c); init = 0)
    isempty(p.c) ? 0 : sum(c -> nleaves_at(c, L), p.c)
end
function guarded_gcd(a::UPoly{CF{B}}, b::UPoly{CF{B}}) where {B}
    while !iszero(b)
        r = monic(rem(a, b))
        nleaves_nested(r) > 2 * max(nleaves_nested(a), nleaves_nested(b)) && return ff_gcd(a, b)
        a, b = b, r
    end
    monic(a)
end
function ff_gcd(a::UPoly{T}, b::UPoly{T}) where {T<:CF}
    iszero(a) && return monic(b)
    iszero(b) && return monic(a)
    (degree(a) == 0 || degree(b) == 0) && return one(a)
    ma, mb = integral_multiplier(T, a.c), integral_multiplier(T, b.c)
    a, b = UPoly{T}(T[c * ma for c in a.c]), UPoly{T}(T[c * mb for c in b.c])
    degree(a) < degree(b) && ((a, b) = (b, a))
    g = h = one(T)
    while true
        δ = degree(a) - degree(b)
        r = prem(a, b)
        iszero(r) && return monic(b)
        degree(r) == 0 && return one(a)
        a, d = b, g * h^δ
        b = UPoly{T}(T[exdiv(c, d) for c in r.c])
        g = lc(a)
        h = δ == 0 ? h : exdiv(g^δ, h^(δ - 1))
    end
end
function resultant(a::UPoly{T}, b::UPoly{T}) where {T<:CF}
    (iszero(a) || iszero(b)) && return zero(T)
    ma, mb = integral_multiplier(T, a.c), integral_multiplier(T, b.c)
    r = ff_resultant(UPoly{T}(T[c * ma for c in a.c]), UPoly{T}(T[c * mb for c in b.c]))
    r / (ma^degree(b) * mb^degree(a))
end

# --- conversions with the nested representation (tests, and the switch in stage 2) ------------------------------
# nested ℚ(t₁, …, tₖ) (cfield(k, B)) → CF{B}
to_cf(::Type{CF{B}}, c::B) where {B} = CF{B}(c)
function to_cf(::Type{CF{B}}, c::Frac{UPoly{S}}) where {B,S}
    j = 1 + cdepth(S)
    t = cf_gen(CF{B}, j)
    ev(p) = (r = zero(CF{B}); for i in length(p.c):-1:1; r = r * t + to_cf(CF{B}, p.c[i]); end; r)
    ev(c.num) / ev(c.den)
end
# CF{B} → nested cfield(k, B), k ≥ the level of c
function from_cf(::Type{C}, c::CF{B}) where {C,B}
    c.lev == 0 && return cfromB(C, c.val)
    t = tgen(C, c.lev)
    ev(p) = (r = zero(C); for i in length(p.c):-1:1; r = r * t + from_cf(C, p.c[i]); end; r)
    ev(c.f.num) / ev(c.f.den)
end
cfromB(::Type{B}, v::B) where {B} = v
cfromB(::Type{Frac{UPoly{S}}}, v) where {S} = kconst(cfromB(S, v))
