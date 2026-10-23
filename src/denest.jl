# ---------------------------------------------------------------------------
# Step DN: denesting square roots. √u with u = a + b√c (a, b, c ∈ ℚ(x), one inner square root) and
# a² - b²c = d² a square in ℚ(x):
#   √(a + b√c) = √p₁ + s√p₂,   p₁ = (a + d)/2, p₂ = (a - d)/2,   s = sign b,
# since (√p₁ + s√p₂)² = p₁ + p₂ + 2s√(p₁p₂) = a + s|b|√c (p₁p₂ = b²c/4). The sign of b (and which of p₁, p₂
# is ≥ 0) is read at a sample point where everything is real: the rewritten integrand, and so the answer,
# is valid on the interval around it where b keeps its sign. Odd powers u^(k/2) = (√u)ᵏ.
# ---------------------------------------------------------------------------

# the term t with its denestable nested square roots rewritten (nothing if there is none)
function denest_rewrite(t, xk::String, b0::Builder)
    changed = Ref(false)
    function walk(s)
        safe_iscall(s) || return s
        args = arguments(s)
        isempty(args) && return s
        rp = radical_parts(s)
        if rp !== nothing && radicand_element(rp[2], xk) === nothing
            r = denest_one(rp[1], rp[2], xk, b0)
            if r !== nothing
                changed[] = true
                return r
            end
        end
        b0.build(op_function(s), (walk(a) for a in args)...)
    end
    r = walk(t)
    changed[] ? r : nothing
end

# u^e (e = k/2) with u = a + b√c denested, or nothing
function denest_one(e::Q, ut, xk::String, b0::Builder)
    k = 2 * e
    isone(denominator(k)) || return nothing
    inner = collect_radicals(ut, xk)
    isempty(inner) && return nothing
    cs = [radicand_element(u, xk) for (_, u) in inner]
    (any(isnothing, cs) || any(c -> c != cs[1], cs) ||
     any(((ei, _),) -> denominator(2 * ei) != 1, inner)) && return nothing
    c = cs[1]
    el = try
        parse_hyp(ut, xk, c, (ue, ei) -> ue == c ? Int(2 * ei) : nothing)
    catch err
        err isa RischNotImplemented || rethrow()
        return nothing
    end
    a, b = el.p, el.q
    iszero(b) && return nothing
    d = csqrt(a * a - b * b * c)
    d === nothing && return nothing
    half = kconst(Q(1, 2))
    p1, p2 = (a + d) * half, (a - d) * half
    # a sample point where c > 0, p₁, p₂ ≥ 0, b ≠ 0 (the interval of the answer)
    ev(f::QXF, x0) = (dn = peval(f.den, x0); iszero(dn) ? nothing : peval(f.num, x0) / dn)
    sgn = nothing
    for x0 in Q.([5 // 2, 37 // 10, 13 // 10, 7 // 10, 6, -3 // 5, -5 // 2, 11, 1 // 3])
        vs = [ev(f, x0) for f in (c, p1, p2, b)]
        any(isnothing, vs) && continue
        cv, v1, v2, bv = vs
        (cv > 0 && v1 >= 0 && v2 >= 0 && !iszero(bv)) || continue
        sgn = Int(sign(bv))
        break
    end
    sgn === nothing && return nothing
    s1, s2 = mk(b0, :sqrt, frac_term(b0, p1)), mk(b0, :sqrt, frac_term(b0, p2))
    r = sgn > 0 ? mk(b0, :+, s1, s2) : mk(b0, :+, s1, mk(b0, :*, b0.lift(-1), s2))
    kk = Int(numerator(k))
    kk == 1 ? r : mk(b0, :^, r, b0.lift(kk))
end
