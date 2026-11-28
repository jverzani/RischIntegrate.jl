# ---------------------------------------------------------------------------
# Step GQ: step GT with symbolic coefficients, x² cos(a + b x²), (d + e x)² sin(a + b x + c x²), f^(a + b x + c x²) sin(d + e x)
#
# f = Σ c xⁿ e^L, L = α x² + β x + δ, as in step GT, but with α, β, δ, c in one constant field K (the parameters,
# log f, cos a, ..., and i), from a tower of the arguments and the x-free subterms of f together. Per L with α ≠ 0,
#   ∫ P e^L = Q e^L + κ_P ∫ e^L,  P = Q′ + L′ Q + κ_P   (deg Q = deg P - 1, solved from the top coefficient down),
#   ∫ e^L = e^κ √π/(2s) erf(s (x + h)),  s² = -α,  h = β/(2α),  κ = δ - β²/(4α)
# (even in s, so any root does: s = (1 ∓ i) √(b/2) for α = ±i b, b real; erfi(√α (x + h)) for a real α printed
# without a leading minus). The elementary part is written with e^(Re L)·(cos, sin)(Im L). Rubi writes the
# answers with FresnelS, FresnelC; these are the same functions in erf form. Checked numerically; nothing when f is
# not of this form, all of α are 0, or step GT (numbers only) applies.
# ---------------------------------------------------------------------------
const GQ_FUNS = (:sin, :cos, :sinh, :cosh, :exp)

function integrate_gaussian_symbolic(f, x; build = nothing, lift = nothing, verify::Bool = true)
    @nospecialize f x
    xk = string(x)
    bd0 = Builder(build === nothing ? auto_build(f, x) : build, lift === nothing ? auto_lift(f, x) : lift, x)
    # the x-free subterms and the arguments (b^u: u log b)
    parts = Any[]
    function walk(t)
        depends_on(t, xk) || (push!(parts, t); return true)
        isnode(t) || return true
        n, as = opname(operation(t)), arguments(t)
        if n in GQ_FUNS && length(as) == 1
            push!(parts, as[1])
            return true
        elseif n === :^ && length(as) == 2 && !depends_on(as[1], xk)
            push!(parts, is_e_const(as[1]) ? as[2] : mk(bd0, :*, as[2], mk(bd0, :log, as[1])))
            return true
        end
        n in (:+, :-, :*, :/, :^) || return false       # (atanh, log, a radical of x: not this step)
        if n === :^
            p = length(as) == 2 ? leaf_rational(as[2]) : nothing
            (p !== nothing && isone(denominator(p)) && (0 <= p <= 12 || (-12 <= p < 0 && string(as[1]) == xk))) || return false
        end
        all(walk, as)
    end
    walk(f) || return nothing
    any(p -> depends_on(p, xk), parts) || return nothing
    # (each argument a polynomial in x by its form, before any tower: e^(e^(e^(e^x))) built a complex tower of four
    # levels and timed out)
    function xpoly(t)
        depends_on(t, xk) || return true
        string(t) == xk && return true
        isnode(t) || return false
        n, as = opname(operation(t)), arguments(t)
        n in (:+, :-, :*) && return all(xpoly, as)
        n === :/ && length(as) == 2 && return xpoly(as[1]) && !depends_on(as[2], xk)
        if n === :^ && length(as) == 2
            p = leaf_rational(as[2])
            return p !== nothing && isone(denominator(p)) && 0 <= p <= 4 && xpoly(as[1])
        end
        false
    end
    all(xpoly, parts) || return nothing
    T = try
        first(build_tower(mk(bd0, :+, parts..., bd0.lift(im)), xk; minimize = false))
    catch err
        (err isa RischNotImplemented || err isa RischError || err isa NotElementary) || rethrow()
        return nothing
    end
    (isempty(T.levels) && is_complex_field(ctype(T))) || return nothing
    try
        gq_integrate(f, x, xk, T, ctype(T), bd0, build, lift, verify)
    catch err
        (err isa RischNotImplemented || err isa RischError || err isa NotElementary || err isa NewConstants ||
         err isa Restart || err isa NeedComplex || err isa DivideError) || rethrow()
        nothing
    end
end

function gq_integrate(f, x, xk, T, ::Type{C}, bd0, build, lift, verify) where {C}
    z, o = zero(C), one(C)
    iC = cimag(C)
    cq(r) = (b = QI(Q(r), Q(0)); C <: CF ? C(b) : cfromB(C, b))   # a rational number of K
    gens = T.consts
    re(c) = (c + cconj_g(gens, c)) / cq(2)
    im_(c) = (c - cconj_g(gens, c)) / (cq(2) * iC)
    isreal_(c) = cconj_g(gens, c) == c
    # an element of K[x] of degree ≤ 2 from a term, as (c₀, c₁, c₂)
    function poly(t)
        el = parse_tower(t, T)
        (isempty(T.levels) && degree(el.den) == 0 && degree(el.num) <= 2) || return nothing
        d = el.den.c[1]
        C[k <= length(el.num.c) ? el.num.c[k] / d : z for k in 1:3]
    end
    # a term as Σ c xⁿ e^(α x² + β x + δ): a vector of ((n, α, β, δ), c)
    Key = Tuple{Int,C,C,C}
    V = Vector{Pair{Key,C}}
    function addto!(v, k, c)
        iszero(c) && return v
        j = findfirst(p -> p.first == k, v)
        if j === nothing
            push!(v, k => c)
        else
            s = v[j].second + c
            iszero(s) ? deleteat!(v, j) : (v[j] = k => s)
        end
        v
    end
    k0 = (0, z, z, z)
    function mul(a, b)
        d = V()
        for (ka, ca) in a, (kb, cb) in b
            addto!(d, (ka[1] + kb[1], ka[2] + kb[2], ka[3] + kb[3], ka[4] + kb[4]), ca * cb)
        end
        d
    end
    function expo(cs, w = o)
        cs === nothing && return nothing
        V([(0, w * cs[3], w * cs[2], w * cs[1]) => o])
    end
    function pr(t)
        if !depends_on(t, xk)
            cs = poly(t)
            cs === nothing && return nothing
            return iszero(cs[1]) ? V() : V([k0 => cs[1]])
        end
        string(t) == xk && return V([(1, z, z, z) => o])
        isnode(t) || return nothing
        n, as = opname(operation(t)), arguments(t)
        if n === :^ && length(as) == 2 && !depends_on(as[1], xk)
            return expo(poly(is_e_const(as[1]) ? as[2] : mk(bd0, :*, as[2], mk(bd0, :log, as[1]))))
        elseif n === :exp && length(as) == 1
            return expo(poly(as[1]))
        elseif n in (:sin, :cos, :sinh, :cosh) && length(as) == 1
            cs = poly(as[1])
            (cs === nothing || !all(isreal_, cs)) && return nothing
            w = n in (:sin, :cos) ? iC : o
            ep, em = expo(cs, w), expo(cs, -w)
            h = o / cq(2)
            n in (:cos, :cosh) && return V([ep[1].first => h, em[1].first => h])
            n === :sinh && return V([ep[1].first => h, em[1].first => -h])
            return V([ep[1].first => h / iC, em[1].first => -h / iC])
        end
        ps = Any[pr(a) for a in as]
        any(isnothing, ps) && return nothing
        if n === :+
            d = V()
            for p in ps, (k, c) in p
                addto!(d, k, c)
            end
            return d
        elseif n === :- && length(ps) == 1
            return V([k => -c for (k, c) in ps[1]])
        elseif n === :- && length(ps) == 2
            d = copy(ps[1])
            for (k, c) in ps[2]
                addto!(d, k, -c)
            end
            return d
        elseif n === :*
            return foldl(mul, ps; init = V([k0 => o]))
        elseif n === :/ && length(ps) == 2
            # a divisor c xᵏ e^L, one term
            length(ps[2]) == 1 || return nothing
            (k, c) = ps[2][1]
            return mul(ps[1], V([(-k[1], -k[2], -k[3], -k[4]) => o / c]))
        elseif n === :^ && length(ps) == 2
            p = leaf_rational(as[2])
            (p !== nothing && isone(denominator(p)) && -12 <= p < 0 && string(as[1]) == xk) && return V([(Int(p), z, z, z) => o])
            (p !== nothing && isone(denominator(p)) && 0 <= p <= 12) || return nothing
            return foldl(mul, fill(ps[1], Int(p)); init = V([k0 => o]))
        end
        nothing
    end
    d = pr(f)
    (d === nothing || isempty(d) || length(d) > 200 || all(p -> iszero(p.first[2]), d)) && return nothing
    # (numbers only: step GT)
    all(p -> p.first[1] >= 0, d) && all(p -> all(c -> crational(re(c)) !== nothing && crational(im_(c)) !== nothing,
                 (p.second, p.first[2], p.first[3], p.first[4])), d) && return nothing
    # the integral: Σ c xᵏ e^L (elementary) + Σ c ∫ e^L
    el = V()
    ef = Vector{Pair{Tuple{C,C,C},C}}()
    function addef!(k, c)
        iszero(c) && return
        j = findfirst(p -> p.first == k, ef)
        j === nothing ? push!(ef, k => c) : (ef[j] = k => ef[j].second + c)
    end
    # xⁿ e^L, n < 0 even, L = α x² + δ: Iₙ = xⁿ⁺¹ e^L/(n + 1) - 2α/(n + 1) Iₙ₊₂ (by parts) down to I₀ (samples 2289, 2290:
    # 1/(a + b asin(c x))^(3/2) through step SQ); odd n ends at ∫ e^L/x, not elementary
    while (j = findfirst(p -> p.first[1] < 0, d); j !== nothing)
        (n, α, β, δ), c = d[j]
        deleteat!(d, j)
        if iszero(α) && iszero(β) && n != -1                # c xⁿ e^δ: c xⁿ⁺¹ e^δ/(n + 1)
            addto!(el, (n + 1, α, β, δ), c / cq(n + 1))
            continue
        end
        (iszero(α) || !iszero(β) || isodd(n)) && return nothing
        addto!(el, (n + 1, α, β, δ), c / cq(n + 1))
        addto!(d, (n + 2, α, β, δ), -cq(2) * α * c / cq(n + 1))
    end
    for ((n, α, β, δ), c) in d
        if iszero(α) && iszero(β)
            addto!(el, (n + 1, α, β, δ), c / cq(n + 1))
        elseif iszero(α)                               # Iₘ = xᵐ e^L/β - (m/β) Iₘ₋₁
            cm = c
            for m in n:-1:0
                addto!(el, (m, α, β, δ), cm / β)
                cm = -cm * cq(m) / β
            end
        else
            # c xⁿ = Q′ + (2α x + β) Q + κ, Q = Σ qⱼ xʲ (j < n): xⁿ: c = 2α q_{n-1}; xʲ⁺¹: 2α qⱼ + β qⱼ₊₁ + (j + 2) qⱼ₊₂ = 0
            q = fill(z, n + 1)                          # q[j + 1] = qⱼ, q[n + 1] = q[n + 2] = 0
            qq(j) = j + 1 <= n ? q[j + 1] : z
            for j in (n - 1):-1:0
                pj1 = j + 1 == n ? c : z
                q[j + 1] = (pj1 - β * qq(j + 1) - cq(j + 2) * qq(j + 2)) / (cq(2) * α)
            end
            κ = (n == 0 ? c : z) - β * qq(0) - qq(1)
            for j in 0:(n - 1)
                addto!(el, (j, α, β, δ), qq(j))
            end
            addef!((α, β, δ), κ)
        end
    end
    bd = Builder(bd0.build, bd0.lift, x, gens)
    X = bd.x
    I_ = bd.lift(im)
    ct(c) = cterm(bd, c)
    function cnum(c)                                   # a + b i, a, b real
        a, b = re(c), im_(c)
        iszero(b) && return ct(a)
        bi = isone(b) ? I_ : mk(bd, :*, ct(b), I_)
        iszero(a) ? bi : mk(bd, :+, ct(a), bi)
    end
    xpow(k) = k == 0 ? nothing : k == 1 ? X : mk(bd, :^, X, bd.lift(k))
    prodt(v) = (v = filter(!isnothing, v); isempty(v) ? bd.lift(1) : length(v) == 1 ? v[1] : mk(bd, :*, v...))
    function lin(a, b, c)                              # a x² + b x + c (real), or nothing for 0
        ts = Any[]
        iszero(a) || push!(ts, prodt(Any[isone(a) ? nothing : ct(a), mk(bd, :^, X, bd.lift(2))]))
        iszero(b) || push!(ts, isone(b) ? X : mk(bd, :*, ct(b), X))
        iszero(c) || push!(ts, ct(c))
        isempty(ts) ? nothing : length(ts) == 1 ? ts[1] : mk(bd, :+, ts...)
    end
    # e^(Re κ) (cos Im κ + i sin Im κ) for a constant κ
    function eκ(κ)
        E, ϕ = lin(z, z, re(κ)), lin(z, z, im_(κ))
        Any[E === nothing ? nothing : mk(bd, :exp, E),
            ϕ === nothing ? nothing : mk(bd, :+, mk(bd, :cos, ϕ), mk(bd, :*, I_, mk(bd, :sin, ϕ)))]
    end
    # the elementary part: (k, Re L, ±Im L, kind) => coefficient, the sign of Im L that of its first entry
    basis = Vector{Pair{Tuple{Int,C,C,C,C,C,C,Symbol},C}}()
    function addb!(k, c)
        iszero(c) && return
        j = findfirst(p -> p.first == k, basis)
        j === nothing ? push!(basis, k => c) : (basis[j] = k => basis[j].second + c)
    end
    for ((k, α, β, δ), c) in el
        R = (re(α), re(β), re(δ))
        Iφ = (im_(α), im_(β), im_(δ))
        s = 1
        if !all(iszero, Iφ)
            j = findfirst(p -> p.first[1] == k && p.first[2:4] == R && p.first[5:7] == map(-, Iφ), basis)
            j === nothing || (s = -1)
        end
        Iφ = s == 1 ? Iφ : map(-, Iφ)
        addb!((k, R..., Iφ..., :cos), c)
        all(iszero, Iφ) || addb!((k, R..., Iφ..., :sin), c * iC * cq(s))   # e^(iφ) = cos φ + i sin φ
    end
    terms = Any[]
    for ((k, ra, rb, rd, ia, ib, id, kind), c) in sort(basis; by = p -> (p.first[1], p.first[8]))
        iszero(c) && continue
        L = lin(ra, rb, rd)
        φ = lin(ia, ib, id)
        push!(terms, prodt(Any[isone(c) ? nothing : cnum(c), xpow(k), L === nothing ? nothing : mk(bd, :exp, L),
                               φ === nothing ? nothing : mk(bd, kind, φ)]))
    end
    sqπ = mk(bd, :sqrt, bd.lift(π))
    for ((α, β, δ), c) in ef
        iszero(c) && continue
        κ = δ - β^2 / (cq(4) * α)
        h = β / (cq(2) * α)
        xh = iszero(h) ? X : mk(bd, :+, X, cnum(h))
        if isreal_(α)
            # erf(√-α (x + h)) / √-α, or erfi(√α (x + h)) / √α
            neg = crational(α) !== nothing ? crational(α) < 0 : startswith(string(ct(α)), "-")
            sq = mk(bd, :sqrt, ct(neg ? -α : α))
            push!(terms, prodt(Any[cnum(c / cq(2)), eκ(κ)..., mk(bd, :/, sqπ, sq), mk(bd, neg ? :erf : :erfi, mk(bd, :*, sq, xh))]))
        else
            b = α / iC
            sq = if isreal_(b)                       # α = i b: s = (1 - i) √(b/2); α = -i b: (1 + i) √(b/2)
                nb = crational(b) !== nothing ? crational(b) < 0 : startswith(string(ct(b)), "-")
                mk(bd, :*, cnum((o + (nb ? iC : -iC)) / cq(2)), mk(bd, :sqrt, ct(cq(2) * (nb ? -b : b))))
            else
                mk(bd, :sqrt, cnum(-α))
            end
            push!(terms, prodt(Any[cnum(c / cq(2)), eκ(κ)..., mk(bd, :/, sqπ, sq), mk(bd, :erf, mk(bd, :*, sq, xh))]))
        end
    end
    isempty(terms) && return nothing
    G = length(terms) == 1 ? terms[1] : mk(bd, :+, terms...)
    (verify && !numeric_antiderivative(f, G, xk)) && return nothing
    G
end
