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

# (the type CF{B}, CFFrac and TField: cf_type.jl, included after fractions.jl)

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
# (the image index of a tower variable over CF: pimage gives the variable of Frac{UPoly{S}} the point of index
# fdepth(S) + 1, above the generators for the nested types; over CF it was 1, t₁'s, and the image test was weak.
# Not a count of generators: those are `nparams`)
fdepth(::Type{CF{B}}) where {B} = 64
# the number of constant generators of the tower (step CK's threshold): the nested depth, or T.consts for CF
nparams(T::Tower) = ctype(T) <: CF ? length(T.consts) : fdepth(ctype(T))
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

# --- CF as the constant field of a tower (stage 2: behind USE_CF) -----------------------------------------------
# build_tower takes CF{base} for ℚ(t₁, …, tₖ), k ≥ 1, when USE_CF[] (else the nested cfield(k, base))
# on by default (stage 3): the precompile workload compiles CF's paths. RISCH_USE_CF=0 when the module is loaded takes
# the nested types, for comparisons
const USE_CF = Ref(true)
__init__() = (haskey(ENV, "RISCH_USE_CF") && (USE_CF[] = ENV["RISCH_USE_CF"] == "1"); nothing)
const_field_type(k::Int, base::Type) = (k >= 1 && USE_CF[]) ? CF{base} : cfield(k, base)
# a field with generators (parameters, e, log p): the nested types or CF
is_tfield(::Type{C}) where {C} = C <: Frac || C <: CF
# the number of generators of C that the RootSum and residue caps count: the depth of the nested type; for CF, the
# highest generator that occurs in the coefficients at hand (the nested depth counts every constant of the tower)
ngens(::Type{C}, cs) where {C} = C <: Frac ? cdepth(C) : C <: CF ? maximum((cf_maxlev(c) for c in cs); init = 0) : 0
# the highest generator in the CF constants of c, through tower elements (Frac, UPoly) to the constants inside
cf_maxlev(c::CF) = c.lev
cf_maxlev(f::Frac) = max(cf_maxlev(f.num), cf_maxlev(f.den))
cf_maxlev(p::UPoly) = maximum((cf_maxlev(c) for c in p.c); init = 0)
cf_maxlev(c) = 0
cf_maxlev(a, b) = max(cf_maxlev(a), cf_maxlev(b))
# nleaves with the CF constants counted at depth K, as in the nested types (K = 0: nleaves)
nleaves_k(c, K::Int) = K == 0 ? nleaves(c) : 1
nleaves_k(c::CF, K::Int) = nleaves_at(c, K)
nleaves_k(f::Frac, K::Int) = nleaves_k(f.num, K) + nleaves_k(f.den, K)
nleaves_k(p::UPoly, K::Int) = isempty(p.c) ? 0 : sum(c -> nleaves_k(c, K), p.c)
ngens(::Type{C}, p::UPoly) where {C} = ngens(C, p.c)

cbase(::Type{CF{B}}) where {B} = B
tgen(::Type{CF{B}}, j::Int) where {B} = cf_gen(CF{B}, j)
cimag(::Type{CF{B}}) where {B} = CF{B}(cimag(B))
crational(c::CF) = c.lev == 0 ? crational(c.val) : nothing
csize(c::CF) = c.lev == 0 ? 1 : csize(c.f)
# the value of c in the subfield of the first d generators, if it lies there
const_below(c::CF, d::Int) = c.lev <= d ? c : nothing

cconj(c::CF{B}) where {B} = c.lev == 0 ? CF{B}(cconj(c.val)) : cf_make(CF{B}, c.lev, cconj(c.f))
function cconj_g(gens, c::CF{B}) where {B}
    c.lev == 0 && return CF{B}(cconj(c.val))
    n, d = cpconj_g(gens, c.f.num), cpconj_g(gens, c.f.den)
    k = c.lev
    (k <= length(gens) && gens[k].kind === :expi) || return cf_make(CF{B}, k, conj_frac(n, d))
    rv(p) = typeof(p)(reverse(p.c))                 # τ ↦ 1/τ
    cf_make(CF{B}, k, conj_frac_rev(rv(n), rv(d), degree(c.f.num), degree(c.f.den)))
end

# ℚ-coordinates of the cs, aligned across the list (as cflat_all of the nested types): all at the highest level L
# of the list, times the lcm of the denominators in t_L, the numerators' coefficients one level down
function cflat_all(::Type{CF{B}}, cs) where {B}
    isempty(cs) && return Vector{Q}[]
    L = maximum((c.lev for c in cs); init = 0)
    L == 0 && return cflat_all(B, B[c.val for c in cs])
    P = UPoly{CF{B}}
    fs = [cf_at(c, L) for c in cs]
    D = reduce(plcm, [f.den for f in fs]; init = one(P))
    nums = [f.num * quo(D, f.den) for f in fs]
    m = maximum(length(n.c) for n in nums)
    parts = [cflat_all(CF{B}, CF{B}[k <= length(n.c) ? n.c[k] : zero(CF{B}) for n in nums]) for k in 1:m]
    [reduce(vcat, (parts[k][j] for k in 1:m); init = Q[]) for j in eachindex(cs)]
end

function csqrt(c::CF{B}) where {B}
    iszero(c) && return c
    if c.lev == 0
        s = csqrt(c.val)
        return s === nothing ? nothing : CF{B}(s)
    end
    a = psqrt(c.f.num)
    a === nothing && return nothing
    b = psqrt(c.f.den)
    b === nothing && return nothing
    cf_make(CF{B}, c.lev, frac(a, b))
end
function constant_roots(p::UPoly{CF{B}}) where {B}
    cf_level0(p) && return [CF{B}(r) for r in constant_roots(to_bpoly(p))]
    constant_roots_generic(p)
end
function const_monomial(c::CF)
    c.lev == 0 && return const_monomial(c.val)
    (is_monomial(c.f.num) && is_monomial(c.f.den)) || return nothing
    inner = const_monomial(lc(c.f.num) / lc(c.f.den))
    inner === nothing && return nothing
    k = degree(c.f.num) - degree(c.f.den)
    iszero(k) ? inner : (inner[1], [inner[2]; (c.lev, k)])
end

# real and complex forms (ℚ(i)(t₁, …) ↔ ℚ(t₁, …))
real_ctype(::Type{CF{QI}}) = CF{Q}
cplx_type(::Type{CF{Q}}) = CF{QI}
function to_real(c::CF{QI})
    if c.lev == 0
        r = to_real(c.val)
        return r === nothing ? nothing : CF{Q}(r)
    end
    n, d = [to_real(a) for a in c.f.num.c], [to_real(a) for a in c.f.den.c]
    (any(isnothing, n) || any(isnothing, d)) && return nothing
    CF{Q}(c.lev, ZERO_Q, CFFrac{Q}(UPoly{CF{Q}}(CF{Q}[n...]), UPoly{CF{Q}}(CF{Q}[d...])))
end
to_complex(::Type{CF{QI}}, r::CF{Q}) = r.lev == 0 ? CF{QI}(to_complex(QI, r.val)) :
    CF{QI}(r.lev, ZERO_QI, CFFrac{QI}(UPoly{CF{QI}}(CF{QI}[to_complex(CF{QI}, a) for a in r.f.num.c]),
                                     UPoly{CF{QI}}(CF{QI}[to_complex(CF{QI}, a) for a in r.f.den.c])))
function cbig(c::CF, gens)
    c.lev == 0 && return cbig(c.val, gens)
    g = gens[c.lev]
    t = g.kind === :exp ? exp(BigFloat(g.arg)) : log(BigFloat(g.arg))
    pe(p) = foldr((a, acc) -> acc * t + cbig(a, gens), p.c; init = BigFloat(0))
    pe(c.f.num) / pe(c.f.den)
end

# Step SD over CF: the factor of D free of the highest generator t_L that occurs
function tfree_factor(D::UPoly{CF{B}}) where {B}
    L = maximum((c.lev for c in D.c); init = 0)
    L == 0 && return nothing
    PB = UPoly{CF{B}}
    fs = [cf_at(c, L) for c in D.c]
    Lc = reduce((a, b) -> quo(a * b, gcd(a, b)), (f.den for f in fs if !iszero(f)); init = one(PB))
    Dh = PB[iszero(f) ? zero(PB) : f.num * quo(Lc, f.den) for f in fs]   # coefficients in (lower)[t_L]
    kmax = maximum(degree(p) for p in Dh)
    G = zero(PB)
    for k in 0:kmax
        Ek = PB(CF{B}[k < length(p.c) ? p.c[k + 1] : zero(CF{B}) for p in Dh])
        iszero(Ek) || (G = iszero(G) ? monic(Ek) : gcd(G, Ek))
    end
    (0 < degree(G) < degree(D)) || return nothing
    G                                                   # (its coefficients are constants of level < L)
end

# c ∈ ℚ(t₁, …, tₖ) as a term: a rational function of t_lev with coefficients of lower levels
function cterm(b::Builder, c::CF)
    c.lev == 0 && return cterm(b, c.val)
    k = c.lev
    k <= length(b.consts) || throw(RischError(
        "constant field with $k generators but only $(length(b.consts)) are described"))
    b.consts[k].kind === :expi && return cterm_expi(b, c.f, b.consts[k].arg)
    t = constgen_term(b, b.consts[k])
    n = cpoly_term(b, c.f.num, t)
    isone(c.f.den) ? n : mk(b, :/, n, cpoly_term(b, c.f.den, t))
end

# √c as a term with a square numerator or denominator (in t_lev) taken out (csqrt_term of the nested types)
function csqrt_term(b::Builder, c::CF{B}) where {B}
    c.lev == 0 && return mk(b, :sqrt, cterm(b, c))
    L = c.lev
    n, d = cf_make(CF{B}, L, frac(c.f.num)), cf_make(CF{B}, L, frac(c.f.den))
    sn, sd = csqrt(n), csqrt(d)
    if sn === nothing && sd === nothing && (csqrt(-n) !== nothing || csqrt(-d) !== nothing)
        n, d = -n, -d                                    # c = (-n)/(-d)
        sn, sd = csqrt(n), csqrt(d)
    end
    nt = sn === nothing ? mk(b, :sqrt, cterm(b, n)) : cterm(b, sn)
    sd === nothing && sn !== nothing && return mk(b, :/, nt, mk(b, :sqrt, cterm(b, d)))
    sd === nothing && return mk(b, :sqrt, cterm(b, c))
    isone(sd) ? nt : mk(b, :/, nt, cterm(b, sd))
end

function cnthroot(c::CF{B}, n::Int) where {B}
    if c.lev == 0
        r = cnthroot(c.val, n)
        return r === nothing ? nothing : CF{B}(r)
    end
    a = pnthroot(c.f.num, n)
    a === nothing && return nothing
    b = pnthroot(c.f.den, n)
    b === nothing ? nothing : cf_make(CF{B}, c.lev, frac(a, b))
end
rational_const(v::CF) = v.lev == 0 ? rational_const(v.val) : nothing
