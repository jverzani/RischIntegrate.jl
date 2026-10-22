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
const MAX_PARAMS = 6          # symbolic parameters (steps SY, PF): see the cap in `parse_tower`
# RootSums over more constant generators than this are refused: their log part (Lazard-Rioboo-Trager over
# ℚ(t₁, …, t₅)) did not finish in minutes for a general quartic, while other integrals with 5, 6 parameters are fast
const MAX_ROOTSUM_GENS = 4

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

# c = r · Π tⱼ^kⱼ (r ∈ ℚ, generators tⱼ of the constant field): (r, [(j, kⱼ)]), else nothing
const_monomial(c::Q) = (c, Tuple{Int,Int}[])
const_monomial(c) = (r = crational(c); r === nothing ? nothing : (r, Tuple{Int,Int}[]))
function const_monomial(c::Frac{<:UPoly})
    (is_monomial(c.num) && is_monomial(c.den)) || return nothing
    inner = const_monomial(lc(c.num) / lc(c.den))
    inner === nothing && return nothing
    k = degree(c.num) - degree(c.den)
    iszero(k) ? inner : (inner[1], [inner[2]; (cdepth(typeof(c)), k)])
end

# log(c) ∈ C for c = r · tₑ^m with r ∈ ℚ, r > 0, m ∈ ℤ, else RischNotImplemented
function const_log(T::Tower, c)
    C = ctype(T)
    gens = T.consts
    (C === Q || C === QI || C <: Frac) || throw(RischNotImplemented(
        "log of the constant $c over the constant field $C is not implemented"))
    # c = r · Π tⱼ^kⱼ: log(tₑ^k) = k/s; log of a parameter a is a generator log(a) of its own (a > 0 is
    # assumed, as for the parameters in radicands)
    mono = const_monomial(c)
    mono === nothing && throw(RischNotImplemented(
        "log of the constant $c: only logs of rationals times powers of e and of parameters are implemented"))
    r, ks = mono
    r > 0 || throw(RischNotImplemented("log of the negative constant $r is complex"))
    val = zero(C)
    missing_ = ConstGen[]
    for (j, k) in ks
        g = gens[j]
        if g.kind === :exp
            val = val + cfromQ(C, k * g.arg)
        elseif g.kind === :sym
            gl = ConstGen(:symlog, Q(0), g.term)
            jl = findfirst(==(gl), gens)
            if jl === nothing
                count(c -> c.kind in (:sym, :symlog), gens) + length(missing_) < MAX_PARAMS || throw(RischNotImplemented(
                    "more than $MAX_PARAMS symbolic parameters and their logs"))
                push!(missing_, gl)
            else
                val = val + k * tgen(C, jl)
            end
        else
            throw(RischNotImplemented("log of the constant $c: a log of $(g.kind) constant $(g.arg)"))
        end
    end
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
