# ---------------------------------------------------------------------------
# Step RC: the reciprocal substitution for one square root of a polynomial P of degree 2m (m even) with
# P(x) = xᵐ S(x + s/x) (coefficients c_{m-k} = sᵏ c_{m+k}, palindromic for s = 1; Rubi 1347):
#   u = x + s/x,  Y = √P/x^(m/2),  Y² = S(u) on every interval.
# For f = R(x)·√Pᵏ (k odd) with h = R x^(km/2)/u′ a function H(u) (symmetric under x ↦ s/x, checked exactly
# by composing), f dx = σ H(u) S(u)^(k/2) du with σ = Y/√S(u) = ±1, constant on each interval:
#   ∫ f = σ G(x + s/x),  G = ∫ H S^(k/2) by the usual route (step PR for parameters).
# ---------------------------------------------------------------------------
const RECIPROCAL = Ref(false)                           # no nested reciprocal substitutions

# the polynomial A with Σ_{k=-m..m} L[k+m+1] xᵏ = A(x + s/x), or nothing
function laurent_to_u(L::Vector{C}, m::Int, s::C) where {C}
    L = copy(L)
    A = zeros(C, m + 1)
    for d in m:-1:0
        c = L[d + m + 1]
        iszero(c) && continue
        A[d + 1] = c
        sj = one(C)
        for j in 0:d                                    # (x + s/x)^d = Σ binom(d, j) sʲ x^(d-2j)
            L[d - 2j + m + 1] -= c * sj * cfromQ(C, Q(binomial(d, j)))
            sj *= s
        end
    end
    all(iszero, L) ? UPoly{C}(A) : nothing
end

# p as a Laurent polynomial about its centre (the mean of its degree and x-valuation): (coefficients, centre)
function laurent_centre(p::UPoly{C}) where {C}
    v = findfirst(!iszero, p.c) - 1
    n = degree(p)
    isodd(n + v) && return nothing
    c = (n + v) ÷ 2
    m = n - c
    (C[i + c + 1 <= length(p.c) && i + c >= 0 ? p.c[i + c + 1] : zero(C) for i in -m:m], m, c)
end

# h = H(x + s/x) for H ∈ C(u): H, or nothing
function symmetric_to_u(h::Frac{UPoly{C}}, s::C) where {C}
    xs = UPoly{C}(C[-s, zero(C), one(C)])                # x² - s = x (x - s/x): an antisymmetric pair made symmetric
    for (N, D) in ((h.num, h.den), (h.num * xs, h.den * xs))
        ln, ld = laurent_centre(N), laurent_centre(D)
        (ln === nothing || ld === nothing || ln[3] != ld[3]) && continue
        A, B = laurent_to_u(ln[1], ln[2], s), laurent_to_u(ld[1], ld[2], s)
        (A === nothing || B === nothing) && continue
        H = frac(A, B)
        uf = frac(UPoly{C}(C[s, zero(C), one(C)]), UPoly{C}(C[zero(C), one(C)]))   # (x² + s)/x
        ev(p) = foldr((c, acc) -> acc * uf + frac(UPoly{C}(C[c])), p.c; init = zero(uf))
        ev(H.num) / ev(H.den) == h && return H
    end
    nothing
end

function try_reciprocal(f, x; build = nothing, lift = nothing, verify::Bool = true)
    @nospecialize f x
    RECIPROCAL[] && return nothing
    xk = string(x)
    rads = [(e, u) for (e, u) in collect_radicals(f, xk) if depends_on(u, xk)]
    (isempty(rads) || length(unique(string(u) for (_, u) in rads)) != 1) && return nothing
    Pt = rads[1][2]
    Ps = string(Pt)
    bd = Builder(build === nothing ? auto_build(f, x) : build, lift === nothing ? auto_lift(f, x) : lift, x)
    # f = R·√Pᵏ
    k, rest = 0, Any[]
    for (t, e) in product_factors!(Any[], f, 1)
        rp = radical_parts(t)
        if rp !== nothing && string(rp[2]) == Ps
            kk = 2 * rp[1] * e
            isone(denominator(kk)) || return nothing
            k += Int(numerator(kk))
        else
            occursin(Ps, string(t)) && return nothing
            push!(rest, (t, e))
        end
    end
    isodd(k) || return nothing
    pw(t, e) = e == 1 ? t : mk(bd, :^, t, bd.lift(e))
    Rt = isempty(rest) ? bd.lift(1) : length(rest) == 1 ? pw(rest[1]...) : mk(bd, :*, (pw(t, e) for (t, e) in rest)...)
    T, Rel, Pel = try
        T, _ = build_tower(mk(bd, :+, Rt, Pt), xk; minimize = false)
        T, parse_tower(Rt, T), parse_tower(Pt, T)
    catch err
        (err isa RischNotImplemented || err isa RischError) || rethrow()
        return nothing
    end
    (isempty(T.levels) && isone(Pel.den)) || return nothing
    C = ctype(T)
    is_complex_field(C) && return nothing
    P = Pel.num
    n = degree(P)
    (n >= 4 && n % 4 == 0) || return nothing
    m = n ÷ 2
    co(i) = i + 1 <= length(P.c) ? P.c[i + 1] : zero(C)
    (iszero(co(m + 1)) || iszero(co(m - 1))) && return nothing
    s = co(m - 1) / co(m + 1)
    S = laurent_to_u(C[co(m + i) for i in -m:m], m, s)
    S === nothing && return nothing
    xp = UPoly{C}(C[zero(C), one(C)])
    h = Rel * frac(xp^(k * m ÷ 2 + 2)) / frac(UPoly{C}(C[-s, zero(C), one(C)]))   # R x^(km/2)/(1 - s/x²)
    H = symmetric_to_u(h, s)
    H === nothing && return nothing
    bc = Builder(bd.build, bd.lift, bd.x, T.consts)
    St = poly_term(bc, S)
    Gt = mk(bc, :*, frac_term(bc, H), mk(bc, :^, St, bc.lift(k // 2)))
    RECIPROCAL[] = true
    G = try
        risch_integrate(Gt, x; build = build, lift = lift, verify = verify)
    catch err
        (err isa RischNotImplemented || err isa NotElementary) || rethrow()
        nothing
    finally
        RECIPROCAL[] = false
    end
    G === nothing && return nothing
    ut = mk(bc, :+, bd.x, mk(bc, :/, cterm(bc, s), bd.x))
    back(t) = isnode(t) ? term_rebuild(bd, t, Any[back(a) for a in arguments(t)]) : (string(t) == xk ? ut : t)
    A = subst_answer(G, back, bd)
    A === nothing && return nothing
    # σ = √P/(x^(m/2) √S(x + s/x))
    xm = m == 2 ? bd.x : mk(bd, :^, bd.x, bd.lift(m ÷ 2))
    σ = mk(bd, :/, mk(bd, :sqrt, Pt), mk(bd, :*, xm, mk(bd, :sqrt, back(St))))
    A isa IntegralWithRootSums || return mk(bd, :*, σ, A)
    IntegralWithRootSums(mk(bd, :*, σ, A.elementary), Any[ScaledRootSum(σ, r) for r in A.rootsums], A.var)
end
