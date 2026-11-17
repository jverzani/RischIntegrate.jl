# ---------------------------------------------------------------------------
# Step RY: one radical y = P^(1/n) with P in an exponential/logarithmic tower K (not in ℚ(x); Rubi 218).
# f is written f = Σ_r A_r yʳ (0 ≤ r < n, A_r ∈ K) by term algebra (sums, products, integer powers, division by
# a monomial a·yᵏ, yⁿ = P). For r > 0 the ansatz ∫ A_r yʳ = B_r yʳ, B_r ∈ K, is the Risch differential equation
#   B_r' + (r/n)(P'/P) B_r = A_r                            ((B yʳ)' = (B' + (r/n) B P'/P) yʳ)
# solved in K (`rde`); A₀ is integrated as usual. No solution for some r: nothing.
# For a square root (n = 2) a denominator c₀ + c₁y is rationalized by its conjugate, and A₁y may have a logarithmic
# part Σ c log((s + y)/(s - y)), whose derivative is y (s P' - 2 P s')/(P (s² - P)) (SymPy #4231, Wikipedia's Risch
# example (1 + 2x + x² + (1 + 3x)√(x + log x))/(x (x + √(x + log x)) √(x + log x))): one term for each simple
# factor S of A₁'s denominator of degree 1 in the top monomial θ, with P(θ₀) = s² a square in K at S's root θ₀ and
# a constant residue c (`ry_logs`). The rest B₁y as above.
# ---------------------------------------------------------------------------

# the square root in K_j of a ∈ K_j, or nothing (coefficients matched from the top, then checked)
function tower_sqrt(T::Tower, j::Int, a)
    iszero(a) && return a
    if j < 0                                            # a constant
        r = crational(a)
        r === nothing && return nothing
        q = rat_sqrt(r)
        return q === nothing ? nothing : cfromQ(ctype(T), q)
    end
    n = poly_sqrt(T, j, a.num)
    n === nothing && return nothing
    d = poly_sqrt(T, j, a.den)
    d === nothing ? nothing : frac(n, d)
end
function poly_sqrt(T::Tower, j::Int, p::UPoly{K}) where {K}
    N = degree(p)
    isodd(N) && return nothing
    h = N ÷ 2
    t = tower_sqrt(T, j - 1, lc(p))
    t === nothing && return nothing
    q = Vector{K}(undef, h + 1)
    q[h + 1] = t
    two_t = t + t
    for k in h-1:-1:0                                   # the coefficient of θ^(h + k) in q²
        acc = p.c[h + k + 1]
        for i in k+1:h
            jj = h + k - i
            (k < jj <= h) && (acc -= q[i + 1] * q[jj + 1])
        end
        q[k + 1] = acc / two_t
    end
    Q2 = UPoly{K}(q)
    Q2 * Q2 == p ? Q2 : nothing
end

# the logarithmic part of ∫ g y, y² = P, g, P ∈ K_m: (terms [(c, s)], g - Σ c (log((s + y)/(s - y)))'/y), or nothing
function ry_logs(T::Tower, m::Int, P, g)
    K = T.Ts[m]
    ev(p, t0) = peval(p, t0)
    terms = Tuple{Any,Any}[]
    PP = P.num * P.den
    for (S, mult) in squarefree(g.den)
        mult == 1 || continue
        G = gcd(S, PP)                                  # (branch points of y, not logs)
        degree(G) > 0 && (S = quo(S, G))
        degree(S) == 0 && continue
        degree(S) == 1 || return nothing               # (no factorization over K here)
        t0 = -S.c[1] / S.c[2]
        Pv = ev(P.num, t0) / ev(P.den, t0)
        s = tower_sqrt(T, m - 1, Pv)
        s === nothing && return nothing
        sm = liftto(T, s, m)
        h = (sm * D(T, m, P) - (P + P) * D(T, m, sm)) / (P * (sm * sm - P))
        Sf = frac(S)
        a, b = g * Sf, h * Sf
        bv = ev(b.num, t0)
        iszero(bv) && return nothing
        c = (ev(a.num, t0) / ev(a.den, t0)) / (bv / ev(b.den, t0))
        const_value(T, liftto(T, c, m)) === nothing && return nothing
        cm = liftto(T, c, m)
        g = g - cm * h
        push!(terms, (cm, sm))
    end
    isempty(terms) ? nothing : (terms, g)
end

function try_tower_radical(f, x; build = nothing, lift = nothing, verify::Bool = true)
    @nospecialize f x
    TOWER_RADICAL[] && return nothing
    xk = string(x)
    rads = [(e, u) for (e, u) in collect_radicals(f, xk) if depends_on(u, xk)]
    (isempty(rads) || length(unique(string(u) for (_, u) in rads)) != 1) && return nothing
    Pt = rads[1][2]
    Ps = string(Pt)
    (isempty(collect_radicals(Pt, xk)) && radicand_element(Pt, xk) === nothing) || return nothing
    n = lcm([Int(denominator(e)) for (e, _) in rads])
    bd = Builder(build === nothing ? auto_build(f, x) : build, lift === nothing ? auto_lift(f, x) : lift, x)
    # f as Dict(k => coefficient term), f = Σ cₖ yᵏ (k ∈ ℤ), or nothing
    one_t = bd.lift(1)
    addto!(d, k, c) = (d[k] = haskey(d, k) ? mk(bd, :+, d[k], c) : c; d)
    function mul(a, b)
        d = Dict{Int,Any}()
        for (i, c) in a, (j, e) in b
            addto!(d, i + j, mk(bd, :*, c, e))
        end
        d
    end
    # 1/(c₀ + c₁y) for a square root (yᵏ = P^q yʳ): its conjugate c₀ - c₁y over c₀² - c₁²P
    function inv_conj(dd)
        n == 2 || return nothing
        cs = Any[nothing, nothing]
        for (k, c) in dd
            q, r = fldmod(k, 2)
            cq = q == 0 ? c : mk(bd, :*, c, mk(bd, :^, Pt, bd.lift(q)))
            cs[r + 1] = cs[r + 1] === nothing ? cq : mk(bd, :+, cs[r + 1], cq)
        end
        any(isnothing, cs) && return nothing
        den = mk(bd, :+, mk(bd, :^, cs[1], bd.lift(2)), mk(bd, :*, bd.lift(-1), mk(bd, :^, cs[2], bd.lift(2)), Pt))
        Dict{Int,Any}(0 => mk(bd, :/, cs[1], den), 1 => mk(bd, :/, mk(bd, :*, bd.lift(-1), cs[2]), den))
    end
    function dec(t)
        occursin(Ps, string(t)) || return Dict{Int,Any}(0 => t)
        rp = radical_parts(t)
        if rp !== nothing && string(rp[2]) == Ps
            k = rp[1] * n
            isone(denominator(k)) || return nothing
            return Dict{Int,Any}(Int(numerator(k)) => one_t)
        end
        safe_iscall(t) || return nothing
        op, args = opname(operation(t)), arguments(t)
        ds = Any[dec(a) for a in args]
        any(isnothing, ds) && return nothing
        if op === :+
            d = Dict{Int,Any}()
            foreach(di -> foreach(((k, c),) -> addto!(d, k, c), di), ds)
            return d
        elseif op === :- && length(ds) == 1
            return Dict{Int,Any}(k => mk(bd, :*, bd.lift(-1), c) for (k, c) in ds[1])
        elseif op === :- && length(ds) == 2
            d = copy(ds[1])
            foreach(((k, c),) -> addto!(d, k, mk(bd, :*, bd.lift(-1), c)), ds[2])
            return d
        elseif op === :*
            return reduce(mul, ds)
        elseif op === :/ && length(ds) == 2
            if length(ds[2]) == 1                            # a monomial a·yᵏ
                (k, c), = ds[2]
                return Dict{Int,Any}(j - k => mk(bd, :/, e, c) for (j, e) in ds[1])
            end
            r = inv_conj(ds[2])
            return r === nothing ? nothing : mul(ds[1], r)
        elseif op === :^ && length(ds) == 2 && length(ds[2]) == 1 && haskey(ds[2], 0)
            p = leaf_rational(args[2])
            (p === nothing || !isone(denominator(p))) && return nothing
            p = Int(numerator(p))
            if length(ds[1]) == 1
                (k, c), = ds[1]
                return Dict{Int,Any}(k * p => mk(bd, :^, c, bd.lift(p)))
            end
            b = ds[1]
            if p < 0                                         # (c₀ + c₁y)⁻ᵖ, as SymJ writes a quotient
                b = inv_conj(b)
                b === nothing && return nothing
                p = -p
            end
            (1 <= p <= 4) || return nothing
            return reduce(mul, fill(b, p))
        end
        nothing
    end
    d = dec(f)
    (d === nothing || all(k -> mod(k, n) == 0, keys(d))) && return nothing
    # yᵏ = P^q yʳ, k = q n + r
    A = Dict{Int,Any}()
    for (k, c) in d
        q, r = fldmod(k, n)
        addto!(A, r, q == 0 ? c : mk(bd, :*, c, mk(bd, :^, Pt, bd.lift(q))))
    end
    T, Pel, Aels = try
        T, _ = build_tower(mk(bd, :+, Pt, values(A)...), xk; minimize = false)
        T, parse_tower(Pt, T), Dict(r => parse_tower(c, T) for (r, c) in A)
    catch err
        (err isa RischNotImplemented || err isa RischError || err isa NeedComplex) || rethrow()
        return nothing
    end
    m = length(T.levels)
    m >= 1 || return nothing
    is_complex_field(ctype(T)) && return nothing        # (no real forms here: trig towers over ℚ(i))
    lift_m(e) = liftto(T, e, m)
    Pm = lift_m(Pel)
    dlogP = D(T, m, Pm) / Pm
    bc = Builder(bd.build, bd.lift, bd.x, T.consts)
    parts = Any[]
    for r in sort!(collect(keys(Aels)))
        r == 0 && continue
        g = lift_m(Aels[r])
        iszero(g) && continue
        fr = dlogP * lconst(T, cfromQ(ctype(T), Q(r) // n), m)
        solve(g) = try
            rde(T, m, fr, g)
        catch err
            (err isa RischNotImplemented || err isa RischError || err isa NotElementary) || rethrow()
            nothing
        end
        B = solve(g)
        if B === nothing && n == 2                     # a logarithmic part first
            lg = ry_logs(T, m, Pm, g)
            lg === nothing && return nothing
            terms, g = lg
            B = iszero(g) ? g : solve(g)
            B === nothing && return nothing
            y = mk(bc, :sqrt, Pt)
            for (c, s) in terms
                st = tower_to_term(bc, T, s)
                push!(parts, mk(bc, :*, tower_to_term(bc, T, c),
                                mk(bc, :log, mk(bc, :/, mk(bc, :+, st, y), mk(bc, :+, st, mk(bc, :*, bc.lift(-1), y))))))
            end
            iszero(B) && continue
        end
        B === nothing && return nothing
        D(T, m, B) + fr * B == g || throw(RischError("internal check failed: step RY"))
        yr = mk(bc, :^, Pt, bc.lift(Q(r) // n))
        push!(parts, mk(bc, :*, tower_to_term(bc, T, B), yr))
    end
    if haskey(A, 0)
        TOWER_RADICAL[] = true
        G = try
            risch_integrate(A[0], x; build = build, lift = lift, verify = verify)
        catch err
            (err isa RischNotImplemented || err isa NotElementary) || rethrow()
            nothing
        finally
            TOWER_RADICAL[] = false
        end
        G === nothing && return nothing
        push!(parts, G)
    end
    add_answers(bd, parts, xk)
end
