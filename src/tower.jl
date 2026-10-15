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
