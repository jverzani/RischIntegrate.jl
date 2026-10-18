# ---------------------------------------------------------------------------
# SI2 phase 1: hyperelliptic curves y² = a(x), a ∈ ℚ[x] squarefree, deg a ≥ 3 (genus ≥ 1)
#
# Integrands rational in x and y = √a. An element is p + q y (p, q ∈ ℚ(x)); {1, y} is an
# integral basis at every finite place (a squarefree). ∫p is a rational integral; by the
# involution y ↦ -y, ∫(p + q y) is elementary iff ∫ q y is. With q y = B/(D y):
#  * Hermite reduction, d(C y/Vᵏ) = (C′aV - kCV′a + CVa′/2)/(V^{k+1} y): for V coprime to a it
#    lowers V^m to V^{m-1} (m ≥ 2); for V | a (ramified places, a = VW) the numerator is
#    V (C′VW + CVW′/2 + (1/2 - k)CV′W), which lowers V^m to V^{m-1} for every m ≥ 1.
#  * reduction at infinity, d(xᵏ y) = (k x^{k-1} a + xᵏ a′/2)/y: deg P ≤ deg a - 2.
# The remainder (P + R/D)/y (D squarefree, coprime to a) has only simple poles. If it has no
# residues it is 0 or not elementary (Liouville: ω = dv with v integral, v = R₁ + R₂ y, and
# deg(R₂′a + R₂a′/2) ≥ deg a - 1 > deg P). Residues need the log part (phase 2, SI2_PLAN.md).
# ---------------------------------------------------------------------------

# p + q y in ℚ(x)(y), y² = a
struct HypEl
    p::QXF
    q::QXF
end
hyp_add(f::HypEl, g::HypEl) = HypEl(f.p + g.p, f.q + g.q)
hyp_neg(f::HypEl) = HypEl(-f.p, -f.q)
hyp_mul(a::QXF, f::HypEl, g::HypEl) = HypEl(f.p * g.p + a * f.q * g.q, f.p * g.q + f.q * g.p)
function hyp_inv(a::QXF, f::HypEl)
    n = f.p * f.p - a * f.q * f.q                       # norm; nonzero since a is not a square
    iszero(n) && throw(DivideError())
    HypEl(f.p / n, -f.q / n)
end
function hyp_pow(a::QXF, f::HypEl, k::Integer)
    k < 0 && return hyp_pow(a, hyp_inv(a, f), -k)
    r, b = HypEl(one(QXF), zero(QXF)), f
    while k > 0
        isodd(k) && (r = hyp_mul(a, r, b))
        k >>= 1
        k > 0 && (b = hyp_mul(a, b, b))
    end
    r
end
# yᵏ
hyp_ypow(a::QXF, k::Integer) = iseven(k) ? HypEl(a^(k ÷ 2), zero(QXF)) : HypEl(zero(QXF), a^((k - 1) ÷ 2))

# the term t as an element of ℚ(x)(y); radval(ue, e) = u^e as a power of y (or nothing)
function parse_hyp(t, xk::String, a::QXF, radval)
    if safe_iscall(t)
        args = arguments(t)
        if !isempty(args)
            rp = radical_parts(t)
            if rp !== nothing
                e, ut = rp
                ue = radicand_element(ut, xk)
                k = ue === nothing ? nothing : radval(ue, e)
                k === nothing && throw(RischNotImplemented("radical $t: not a power of √($a)"))
                return hyp_ypow(a, k)
            end
            n = opname(operation(t))
            v = HypEl[parse_hyp(u, xk, a, radval) for u in args]
            n === :+ && return foldl(hyp_add, v)
            n === :- && return length(v) == 1 ? hyp_neg(v[1]) : hyp_add(v[1], hyp_neg(foldl(hyp_add, v[2:end])))
            n === :* && return foldl((f, g) -> hyp_mul(a, f, g), v)
            n === :/ && length(v) == 2 && return hyp_mul(a, v[1], hyp_inv(a, v[2]))
            n === :inv && length(v) == 1 && return hyp_inv(a, v[1])
            if n === :^ && length(v) == 2
                k = iszero(v[2].q) ? const_int(v[2].p) : nothing
                (k === nothing || abs(k) > 10_000) &&
                    throw(RischNotImplemented("only small integer powers are supported over √($a)"))
                return hyp_pow(a, v[1], k)
            end
            throw(RischNotImplemented("`$n` in an integrand over √($a): only rational functions of x and √a are supported"))
        end
    end
    string(t) == xk && return HypEl(frac(xpoly(Q)), zero(QXF))
    r = leaf_rational(t)
    r !== nothing && return HypEl(kconst(r), zero(QXF))
    throw(RischNotImplemented("symbol `$t` is not the integration variable"))
end

# C ≡ B / M mod V
function hyp_solve_mod(B::QX, M::QX, V::QX)
    s, _, g = gcdex(rem(M, V), V)
    isone(g) || throw(RischError("hyperelliptic Hermite reduction: gcd(M, V) ≠ 1"))
    rem(s * B, V)
end

# ∫ B/(D y) dx = g y + ∫ (P + R/D)/y dx, D squarefree and coprime to a, deg P ≤ deg a - 2
function hyp_reduce(a::QX, B::QX, D::QX)
    g = zero(QXF)
    da = deriv(a)
    while true
        h = gcd(B, D)
        degree(h) > 0 && (B = quo(B, h); D = quo(D, h))
        step = nothing
        for (V0, m) in squarefree(D)
            Va = gcd(V0, a)
            Vc = quo(V0, Va)
            if degree(Va) > 0                           # ramified: V^m → V^{m-1}, k = m
                step = (Va, m, true)
                break
            elseif m >= 2 && degree(Vc) > 0            # V^m → V^{m-1}, k = m - 1
                step = (Vc, m, false)
                break
            end
        end
        step === nothing && break
        V, m, ram = step
        Ds = quo(D, V^m)
        dV = deriv(V)
        if ram
            W = quo(a, V)
            k = m
            Cc = hyp_solve_mod(B, scale(Q(1) // 2 - k, Ds * dV * W), V)
            # d(C y/Vᵏ) = (C′VW + CVW′/2 + (1/2 - k)CV′W)/(Vᵏ y)
            Nn = deriv(Cc) * V * W + scale(Q(1) // 2, Cc * V * deriv(W)) + scale(Q(1) // 2 - k, Cc * dV * W)
        else
            k = m - 1
            Cc = hyp_solve_mod(B, scale(Q(-k), Ds * dV * a), V)
            # d(C y/Vᵏ) = (C′aV - kCV′a + CVa′/2)/(V^{k+1} y)
            Nn = deriv(Cc) * a * V - scale(Q(k), Cc * dV * a) + scale(Q(1) // 2, Cc * V * da)
        end
        g = g + frac(Cc, V^k)
        r, z = divrem(B - Ds * Nn, V)
        iszero(z) || throw(RischError("hyperelliptic Hermite reduction: numerator not divisible"))
        B, D = r, Ds * V^(m - 1)
    end
    P, R = divrem(B, D)
    n = degree(a)
    while degree(P) >= n - 1                            # at infinity: d(xᵏ y)
        k = degree(P) - n + 1
        c = lc(P) / (lc(a) * (k + Q(n) // 2))
        xk = xpoly(Q)^k
        dk = (k == 0 ? zero(QX) : scale(Q(k), xpoly(Q)^(k - 1) * a)) + scale(Q(1) // 2, xk * da)
        P = P - scale(c, dk)
        g = g + frac(scale(c, xk))
    end
    g, P, R, D
end

# residues of (P + R/D)/y: none iff R = 0 and (deg a odd or P has no x^{deg a/2 - 1} term)
function hyp_residue_free(a::QX, P::QX, R::QX)
    iszero(R) || return false
    n = degree(a)
    isodd(n) && return true
    j = n ÷ 2 - 1
    j > degree(P) || iszero(P.c[j + 1])
end

# genus of y² = a, a squarefree
hyp_genus(a::QX) = (degree(a) - 1) ÷ 2

# The hook from `integrate_radical`: one radicand u ∈ ℚ[x] of degree ≥ 3, square roots only.
# radval(ue, e) = the exponent k with ue^e = yᵏ, or nothing.
function integrate_hyperelliptic(f, xk::String, u::QXF, uterm, radval, b0::Builder, verify::Bool)
    a = u.num
    isone(u.den) && degree(a) >= 3 || throw(RischError("integrate_hyperelliptic: not a polynomial radicand"))
    sf = squarefree(a)
    all(((_, m),) -> m == 1, sf) || throw(RischNotImplemented(
        "√($uterm): radicands with repeated factors of degree ≥ 3 are not supported yet"))
    el = parse_hyp(f, xk, u, radval)
    q = el.q
    B, D = q.num * a, q.den                             # q y = q a / y
    g, P, R, D = hyp_reduce(a, B, D)
    # exact check: d(g y) = (g′a + g a′/2)/y must equal q y - (P + R/D)/y, i.e. (q a - P - R/D)/y
    if verify
        dgy = dx(g) * u + g * frac(scale(Q(1) // 2, deriv(a)))
        dgy == q * u - frac(P) - frac(R, D) ||
            throw(RischError("internal check failed: hyperelliptic Hermite reduction"))
    end
    rest_zero = iszero(P) && iszero(R)
    if !rest_zero
        hyp_residue_free(a, P, R) && throw(NotElementary(
            "after Hermite reduction ∫ ($(zpoly_string(P, xk)))/√($uterm) is left: a nonzero differential " *
            "without residues on a curve of genus $(hyp_genus(a))"))
        throw(RischNotImplemented(
            "√($uterm): the remainder after Hermite reduction has residues; the logarithmic part on a " *
            "curve of genus $(hyp_genus(a)) is not implemented yet (SI2 phase 2)"))
    end
    yterm = mk(b0, :sqrt, uterm)
    alg = iszero(g) ? nothing : mk(b0, :*, frac_term(b0, g), yterm)
    iszero(el.p) && return alg === nothing ? b0.lift(0) : alg
    T, _ = build_tower(b0.x, xk)
    F = integrate_built(T, el.p, b0, verify)
    alg === nothing && return F
    F isa IntegralWithRootSums && return IntegralWithRootSums(mk(b0, :+, F.elementary, alg), F.rootsums, F.var)
    mk(b0, :+, F, alg)
end
