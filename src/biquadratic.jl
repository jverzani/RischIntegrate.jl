# ---------------------------------------------------------------------------
# Two square roots y = √a, z = √b (a, b ∈ ℚ(x), ab not a square): the biquadratic field
# K = ℚ(x)(y, z), basis 1, y, z, yz, Galois group {1, σ_a, σ_b, σ_aσ_b} (sign changes of y, z).
# f = f₀ + f₁y + f₂z + f₃yz, and the four parts are the projections (1/4)Σ χ(τ) τ(f) for the four
# characters χ. If ∫f is elementary, f = v′ + Σ cᵢ uᵢ′/uᵢ (Liouville, over K(c̄)) and projecting gives
# fⱼ·(basis) = π(v)′ + Σ cᵢ (1/4) d log Π_τ τ(uᵢ)^χ(τ), elementary over the fixed field of ker χ: the
# quadratic subfields ℚ(x)(y), ℚ(x)(z), ℚ(x)(yz). So ∫f is elementary iff each part is, and each part
# is a one-radicand problem (√a, √b, √(ab)). The part f₃yz is integrated as f₃√(ab); its answer only
# uses Y² = ab, so √(ab) is then written back as √a·√b (valid on every branch).
# ---------------------------------------------------------------------------

# f₀ + f₁y + f₂z + f₃yz
struct BiqEl
    c::NTuple{4,QXF}
end
biq_add(u::BiqEl, v::BiqEl) = BiqEl(u.c .+ v.c)
biq_neg(u::BiqEl) = BiqEl(map(-, u.c))
function biq_mul(a::QXF, b::QXF, u::BiqEl, v::BiqEl)
    (p0, p1, p2, p3), (q0, q1, q2, q3) = u.c, v.c
    BiqEl((p0 * q0 + a * p1 * q1 + b * p2 * q2 + a * b * p3 * q3,
           p0 * q1 + p1 * q0 + b * (p2 * q3 + p3 * q2),
           p0 * q2 + p2 * q0 + a * (p1 * q3 + p3 * q1),
           p0 * q3 + p3 * q0 + p1 * q2 + p2 * q1))
end
biq_conj(u::BiqEl, sy::Int, sz::Int) = BiqEl((u.c[1], sy * u.c[2], sz * u.c[3], sy * sz * u.c[4]))
function biq_inv(a::QXF, b::QXF, u::BiqEl)
    c = biq_mul(a, b, biq_mul(a, b, biq_conj(u, -1, 1), biq_conj(u, 1, -1)), biq_conj(u, -1, -1))
    n = biq_mul(a, b, u, c).c[1]                        # the norm, in ℚ(x)
    iszero(n) && throw(DivideError())
    BiqEl(map(t -> t / n, c.c))
end
biq_const(f::QXF) = BiqEl((f, zero(QXF), zero(QXF), zero(QXF)))
function biq_pow(a, b, u::BiqEl, k::Integer)
    k < 0 && return biq_pow(a, b, biq_inv(a, b, u), -k)
    r, s = biq_const(one(QXF)), u
    while k > 0
        isodd(k) && (r = biq_mul(a, b, r, s))
        k >>= 1
        k > 0 && (s = biq_mul(a, b, s, s))
    end
    r
end
# y^i z^j
function biq_ypow(a::QXF, b::QXF, i::Int, j::Int)
    ca, cb = a^fld(i, 2), b^fld(j, 2)
    v = [zero(QXF) for _ in 1:4]
    v[1 + mod(i, 2) + 2 * mod(j, 2)] = ca * cb
    BiqEl(Tuple(v))
end

# the term t in K; radval(ue, e) = (i, j) with ue^e = y^i z^j, or nothing
function parse_biq(t, xk::String, a::QXF, b::QXF, radval)
    if safe_iscall(t)
        args = arguments(t)
        if !isempty(args)
            rp = radical_parts(t)
            if rp !== nothing
                ue = radicand_element(rp[2], xk)
                ij = ue === nothing ? nothing : radval(ue, rp[1])
                ij === nothing && throw(RischNotImplemented("radical $t: not a power of √a or √b"))
                return biq_ypow(a, b, ij...)
            end
            n = opname(operation(t))
            v = BiqEl[parse_biq(u, xk, a, b, radval) for u in args]
            n === :+ && return foldl(biq_add, v)
            n === :- && return length(v) == 1 ? biq_neg(v[1]) : biq_add(v[1], biq_neg(foldl(biq_add, v[2:end])))
            n === :* && return foldl((f, g) -> biq_mul(a, b, f, g), v)
            n === :/ && length(v) == 2 && return biq_mul(a, b, v[1], biq_inv(a, b, v[2]))
            n === :inv && length(v) == 1 && return biq_inv(a, b, v[1])
            if n === :^ && length(v) == 2
                c = v[2].c
                k = all(iszero, c[2:4]) ? const_int(c[1]) : nothing
                (k === nothing || abs(k) > 10_000) && throw(RischNotImplemented("only small integer powers are supported"))
                return biq_pow(a, b, v[1], k)
            end
            throw(RischNotImplemented("`$n` with two square roots: only rational functions of x, √a and √b are supported"))
        end
    end
    string(t) == xk && return biq_const(frac(xpoly(Q)))
    r = leaf_rational(t)
    r !== nothing && return biq_const(kconst(r))
    throw(RischNotImplemented("symbol `$t` is not the integration variable"))
end

# ∫ f for radicals of the two radicands of `groups` (both square roots); pmap: radicand powers (RP)
function integrate_biquadratic(f, x, xk::String, groups, b0::Builder, verify::Bool, pmap)
    (a, aterm, _), (b, bterm, _) = groups
    radval = function (ue, e)
        k = 2 * e
        w, m = ue == a || ue == b ? (ue, 1) : get(pmap, ue, (nothing, 0))
        w === nothing && return nothing
        k *= m
        isone(denominator(k)) || return nothing
        w == a ? (Int(numerator(k)), 0) : w == b ? (0, Int(numerator(k))) : nothing
    end
    el = parse_biq(f, xk, a, b, radval)
    f0, f1, f2, f3 = el.c
    ab = a * b
    abterm = frac_term(b0, ab)
    kw = (build = b0.build, lift = b0.lift, verify = verify)
    parts = Any[]
    iszero(f0) || push!(parts, risch_integrate(frac_term(b0, f0), x; kw...))
    iszero(f1) || push!(parts, risch_integrate(mk(b0, :*, frac_term(b0, f1), mk(b0, :sqrt, aterm)), x; kw...))
    iszero(f2) || push!(parts, risch_integrate(mk(b0, :*, frac_term(b0, f2), mk(b0, :sqrt, bterm)), x; kw...))
    if !iszero(f3)
        F3 = risch_integrate(mk(b0, :*, frac_term(b0, f3), mk(b0, :sqrt, abterm)), x; kw...)
        yz = mk(b0, :*, mk(b0, :sqrt, aterm), mk(b0, :sqrt, bterm))
        back(t) = biq_rewrite(t, xk, ab, yz, b0)
        F3 = F3 isa IntegralWithRootSums ?
             IntegralWithRootSums(back(F3.elementary), Any[biq_rewrite_rs(r, back) for r in F3.rootsums], F3.var) :
             back(F3)
        push!(parts, F3)
    end
    isempty(parts) && return b0.lift(0)
    E, rss = Any[], Any[]
    for p in parts
        if p isa IntegralWithRootSums
            push!(E, p.elementary)
            append!(rss, p.rootsums)
        else
            push!(E, p)
        end
    end
    Et = length(E) == 1 ? E[1] : mk(b0, :+, E...)
    isempty(rss) ? Et : IntegralWithRootSums(Et, rss, xk)
end

# √(ab)^k ↦ (√a √b)^k in a term
function biq_rewrite(t, xk::String, ab, yz, b0::Builder)
    safe_iscall(t) || return t
    args = arguments(t)
    isempty(args) && return t
    rp = radical_parts(t)
    if rp !== nothing && radicand_element(rp[2], xk) == ab
        k = 2 * rp[1]
        isone(denominator(k)) && return isone(k) ? yz : mk(b0, :^, yz, b0.lift(Int(numerator(k))))
    end
    b0.build(op_function(t), (biq_rewrite(s, xk, ab, yz, b0) for s in args)...)
end
biq_rewrite_rs(r::TermRootSum, back) =
    TermRootSum(r.poly, Any[c === nothing ? nothing : c isa Tuple ? map(t -> t === nothing ? nothing : back(t), c) : back(c)
                            for c in r.coeffs], r.var, r.pterms)
biq_rewrite_rs(r::ScaledRootSum, back) = ScaledRootSum(back(r.factor), biq_rewrite_rs(r.rs, back))
biq_rewrite_rs(r, back) = r                             # RootSums in x only: no radicals
