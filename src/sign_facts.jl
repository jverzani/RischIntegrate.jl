# ---------------------------------------------------------------------------
# Step SO, `signs`: signs of parameter expressions given as facts, the way GruntzLimit takes them: pairs
# c => s, c a parameter or an expression in the parameters (written like f), s one of :positive,
# :negative, :nonzero. They make a sign oracle (the `sign` keyword): an
# expression asked about is read, like the facts, as a quotient of sparse polynomials over ℚ in the
# parameters, and its sign is decided
#   * by a fact about λ c (λ ∈ ℚ),
#   * term by term: every term of the numerator, and of the denominator, of one sign, from the signs of
#     the parameters (an even power of a parameter is positive),
#   * as a product: numerator and denominator λ times products of powers of the facts' expressions and
#     the parameters (exact division by each in turn; a :nonzero one to an even power);
# else it is undecided (nothing). GruntzLimit's :nonnegative, :nonpositive and :zero are not taken (an
# ArgumentError): a zero value is a special case of the parameters, which is not treated (GruntzLimit
# substitutes the solution of c = 0 for a parameter).
# ---------------------------------------------------------------------------

const SMono = Vector{Pair{String,Int}}                  # sorted by name, exponents ≥ 1
const SPoly = Dict{SMono,Q}

function smono_mul(a::SMono, b::SMono)
    out, i, j = SMono(), 1, 1
    while i <= length(a) || j <= length(b)
        if j > length(b) || (i <= length(a) && a[i].first < b[j].first)
            push!(out, a[i]); i += 1
        elseif i > length(a) || b[j].first < a[i].first
            push!(out, b[j]); j += 1
        else
            push!(out, a[i].first => a[i].second + b[j].second); i += 1; j += 1
        end
    end
    out
end
# a / b, or nothing when b does not divide a
function smono_div(a::SMono, b::SMono)
    d = Dict(a)
    for (v, e) in b
        get(d, v, 0) >= e || return nothing
        d[v] -= e
    end
    sort!([v => e for (v, e) in d if e > 0]; by = first)
end
# lexicographic order, the variables alphabetically: whether a < b
function smono_less(a::SMono, b::SMono)
    i = 1
    while true
        i > length(a) && return i <= length(b)
        i > length(b) && return false
        (va, ea), (vb, eb) = a[i], b[i]
        va == vb || return va > vb                      # (b has the earlier variable, a does not)
        ea == eb || return ea < eb
        i += 1
    end
end

sconst(c) = iszero(c) ? SPoly() : SPoly(SMono() => Q(c))
function sadd(a::SPoly, b::SPoly, s = 1)
    r = copy(a)
    for (m, c) in b
        v = get(r, m, Q(0)) + s * c
        iszero(v) ? delete!(r, m) : (r[m] = v)
    end
    r
end
function smul(a::SPoly, b::SPoly)
    r = SPoly()
    for (m, c) in a, (n, d) in b
        k = smono_mul(m, n)
        v = get(r, k, Q(0)) + c * d
        iszero(v) ? delete!(r, k) : (r[k] = v)
    end
    r
end
spow(a::SPoly, n::Int) = foldl((p, _) -> smul(p, a), 1:n; init = sconst(1))
slead(a::SPoly) = foldl((x, y) -> smono_less(x[1], y[1]) ? y : x, collect(a))
# a / b when b divides a, else nothing
function sdiv(a::SPoly, b::SPoly)
    q, r = SPoly(), a
    mb, cb = slead(b)
    while !isempty(r)
        mr, cr = slead(r)
        m = smono_div(mr, mb)
        m === nothing && return nothing
        t = SPoly(m => cr / cb)
        q, r = sadd(q, t), sadd(r, smul(t, b), -1)
    end
    q
end
# λ with a = λ b, or nothing
function sratio(a::SPoly, b::SPoly)
    (isempty(a) || isempty(b) || length(a) != length(b)) && return nothing
    m, c = first(a)
    haskey(b, m) || return nothing
    λ = c / b[m]
    all(((n, d),) -> get(b, n, Q(0)) * λ == d, a) ? λ : nothing
end

# the term t as (N, D), N/D with N, D ∈ ℚ[parameters], or nothing (a function other than +, -, *, /, an
# integer power)
function read_spoly_frac(t)
    r = leaf_rational(t)
    r === nothing || return (sconst(r), sconst(1))
    if !safe_iscall(t)
        s = string(t)
        s in ("pi", "π", "ℯ", "e", "im", "I") && return nothing
        return (SPoly(SMono([s => 1]) => Q(1)), sconst(1))
    end
    op, args = opname(operation(t)), arguments(t)
    rs = Any[read_spoly_frac(a) for a in args]
    any(isnothing, rs) && op !== :^ && return nothing
    if op === :+
        return foldl(((n1, d1), (n2, d2)) -> (sadd(smul(n1, d2), smul(n2, d1)), smul(d1, d2)), rs)
    elseif op === :- && length(rs) == 1
        return (sadd(SPoly(), rs[1][1], -1), rs[1][2])
    elseif op === :-
        (n1, d1), (n2, d2) = rs
        return (sadd(smul(n1, d2), smul(n2, d1), -1), smul(d1, d2))
    elseif op === :*
        return foldl(((n1, d1), (n2, d2)) -> (smul(n1, n2), smul(d1, d2)), rs)
    elseif op === :/ && length(rs) == 2
        (n1, d1), (n2, d2) = rs
        isempty(n2) && return nothing
        return (smul(n1, d2), smul(d1, n2))
    elseif op === :^ && length(args) == 2 && rs[1] !== nothing
        e = leaf_rational(args[2])
        (e === nothing || !isone(denominator(e)) || abs(e) > 64) && return nothing
        n, d = rs[1]
        k = Int(numerator(e))
        k < 0 && isempty(n) && return nothing
        return k >= 0 ? (spow(n, k), spow(d, k)) : (spow(d, -k), spow(n, -k))
    end
    nothing
end

const SIGN_FACT_VALUES = Dict(:positive => 1, :negative => -1, :nonzero => 0)

struct SignFacts
    facts::Vector{Tuple{SPoly,SPoly,Int}}               # (N, D, sign); sign 0: nonzero
    params::Dict{String,Int}                            # the parameters of known sign
end

function SignFacts(signs)
    facts = Tuple{SPoly,SPoly,Int}[]
    for (c, s) in signs
        s in (:zero, :nonnegative, :nonpositive) && throw(ArgumentError(
            "signs: $s for $c is not taken: a zero value is a special case of the parameters, which the integrator does not treat (substitute it, or give :positive or :negative)"))
        haskey(SIGN_FACT_VALUES, s) || throw(ArgumentError("signs: $s for $c; one of :positive, :negative, :nonzero expected"))
        r = read_spoly_frac(c)
        (r === nothing || isempty(r[1])) &&
            throw(ArgumentError("signs: $c is not a rational expression in the parameters"))
        push!(facts, (r[1], r[2], SIGN_FACT_VALUES[s]))
    end
    params = Dict{String,Int}()
    for (n, d, s) in facts
        (s != 0 && length(n) == 1 && length(d) == 1 && isempty(first(d)[1])) || continue
        m, c = first(n)
        length(m) == 1 && m[1].second == 1 || continue
        params[m[1].first] = s * Int(sign(c)) * Int(sign(first(d)[2]))
    end
    SignFacts(facts, params)
end

# the sign of every term of p, if they share one
function sterms_sign(F::SignFacts, p::SPoly)
    out = nothing
    for (m, c) in p
        s = Int(sign(c))
        for (v, e) in m
            iseven(e) && continue
            sv = get(F.params, v, nothing)
            sv === nothing && return nothing
            s *= sv
        end
        out === nothing ? (out = s) : (out == s || return nothing)
    end
    out
end
# the sign of p as λ times a product of powers of the facts' polynomial expressions (and parameters)
function sproduct_sign(F::SignFacts, p::SPoly)
    s, odd = 1, Set{Int}()
    for (k, (n, d, sk)) in enumerate(F.facts)
        (length(d) == 1 && isempty(first(d)[1]) && !(length(n) == 1 && isempty(first(n)[1]))) || continue
        while (q = sdiv(p, n)) !== nothing
            p = q
            sk == 0 ? (k in odd ? delete!(odd, k) : push!(odd, k)) : (s *= sk * Int(sign(first(d)[2])))
        end
    end
    for (v, sv) in F.params
        while (q = sdiv(p, SPoly(SMono([v => 1]) => Q(1)))) !== nothing
            p, s = q, s * sv
        end
    end
    (isempty(odd) && length(p) == 1 && isempty(first(p)[1])) ? s * Int(sign(first(p)[2])) : nothing
end

function facts_sign(F::SignFacts, t)
    r = read_spoly_frac(t)
    r === nothing && return nothing
    N, D = r
    isempty(N) && return nothing
    for (n, d, s) in F.facts
        s == 0 && continue
        λ = sratio(smul(N, d), smul(n, D))
        λ === nothing || return s * Int(sign(λ))
    end
    sN, sD = sterms_sign(F, N), sterms_sign(F, D)
    sN !== nothing && sD !== nothing && return sN * sD
    sN, sD = sproduct_sign(F, N), sproduct_sign(F, D)
    sN !== nothing && sD !== nothing ? sN * sD : nothing
end
