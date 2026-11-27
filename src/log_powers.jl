# ---------------------------------------------------------------------------
# Step LG: ∫ Σₖ sₖ(x) θᵏ, θ = log v, v = α x + β (α, β ∈ C), sₖ ∈ C(x), when the logarithmic part needs logarithms
# other than θ (∫ log²(x)/(d + e x), ∫ (a + b log(c x))²/(d + e x), ∫ log(c (a + b x)ⁿ)/(d + e x²)). From the top
# power down: Hermite reduction gives sₖ = g′ + Q + R/D (Q a polynomial, D squarefree); with G = ∫ Q,
#   ∫ (g′ + Q) θᵏ = (g + G) θᵏ - k ∫ (g + G) θ′ θᵏ⁻¹       (the second integral joins s_{k-1}),
# the pole of R/D at v = 0 (x₀ = -β/α), c₀/(x - x₀) = c₀ θ′: c₀ θᵏ⁺¹/(k + 1), and each other root c of D, residue ρ,
# K = α c + β ≠ 0 (v - K = α (x - c)):
#   ∫ θᵏ/(x - c) = θᵏ log(1 - v/K) + k Σ_{l=0}^{k-1} (-1)ˡ (k-1)!/(k-1-l)! θ^(k-1-l) Li_{l+2}(v/K).
# s₀ is a rational function, integrated as usual. Roots c: in C, or of quadratic factors (and quadratics in x²),
# ρ and 1/K computed modulo the factor and printed at c = -p/2 ± √δ (as step PX). The answer is in complex form,
# as Rubi writes it, and is checked numerically (F′ = f at real points, zero imaginary parts as +0).
# ---------------------------------------------------------------------------
const MAX_LG_POWER = 6

function try_log_powers(f, x; build = nothing, lift = nothing, verify::Bool = true)
    @nospecialize f x
    (PX_ACTIVE[] || ATAN_SUBST[] || XPARTS[] != 0) && return nothing
    xk = string(x)
    T, el = try
        build_tower(f, xk)
    catch e
        (e isa RischNotImplemented || e isa RischError || e isa NotElementary) && return nothing
        rethrow()
    end
    if length(T.levels) != 1                            # U^n/V^n in the logarithm as (U/V)^n (samples 1223, 1224)
        f2 = combine_log_powers(f, x, xk, build, lift)
        f2 === nothing && return nothing
        G = try_log_powers(f2, x; build = build, lift = lift, verify = verify)
        (G === nothing || (verify && !numeric_antiderivative(f, G, xk; pz = true))) && return nothing
        return G
    end
    (T.levels[1].kind === :log && levelof(T, el) == 1) || return nothing
    C = ctype(T)
    arg = T.levels[1].arg                               # v ∈ C(x)
    if !(degree(arg.den) == 0 && degree(arg.num) == 1)
        (degree(arg.num) <= 1 && degree(arg.den) == 1) || return nothing
        return log_powers_mobius(f, x, T, arg, build, lift, verify)
    end
    l0 = arg.den.c[1]
    β, α = arg.num.c[1] / l0, arg.num.c[2] / l0
    degree(el.den) == 0 || return nothing
    m = degree(el.num)
    (1 <= m <= MAX_LG_POWER) || return nothing
    d0 = el.den.c[1]
    s = Any[el.num.c[k + 1] / d0 for k in 0:m]          # sₖ ∈ K = C(x)
    bd = Builder(build === nothing ? auto_build(f, x) : build, lift === nothing ? auto_lift(f, x) : lift, x, T.consts)
    PX_ACTIVE[] = true                                  # (no nested step LG, PX)
    G = try
        Base.ScopedValues.with(COMPLEX_OUT => true) do
            log_powers_answer(bd, T, s, α, β, x, build, lift, verify)
        end
    catch e
        (e isa NotElementary || e isa RischNotImplemented) || rethrow()
        nothing
    finally
        PX_ACTIVE[] = false
    end
    G === nothing && return nothing
    (verify && !numeric_antiderivative(f, G, xk; pz = true)) && return nothing
    G
end

function log_powers_answer(b::Builder, T::Tower, s, α, β, x, build, lift, verify)
    C = ctype(T)
    P = UPoly{C}
    K = T.Ts[1]
    θt = theta_term(b, T, 1)
    vt = tower_to_term(b, T, T.levels[1].arg)
    xt(w) = tower_to_term(b, T, w)
    θpow(k) = k == 0 ? nothing : k == 1 ? θt : mk(b, :^, θt, b.lift(k))
    mul(t, u) = t === nothing ? u : u === nothing ? t : mk(b, :*, t, u)
    dθ = frac(P(C[α]), P(C[β, α]))                      # θ′ = α/(α x + β)
    x0 = -β / α
    lin0 = P(C[-x0, one(C)])
    ts = Any[]
    m = length(s) - 1
    for k in m:-1:1
        sk = s[k + 1]
        iszero(sk) && continue
        g, Qp, R, Dsf = hermite_reduce(deriv, sk.num, sk.den)
        Gq = frac(integrate_poly(Qp))
        gG = g + Gq
        if !iszero(gG)
            push!(ts, mul(xt(gG), θpow(k)))
            s[k] = s[k] - cfromQ_frac(C, k) * gG * dθ   # -k (g + G) θ′ into s_{k-1}
        end
        iszero(R) && continue
        if iszero(rem(Dsf, lin0))                       # c₀/(x - x₀): c₀ θᵏ⁺¹/(k + 1)
            D1 = quo(Dsf, lin0)
            c0 = peval(R, x0) / peval(D1, x0)
            push!(ts, mul(cterm(b, c0 / cfromQ(C, Q(k + 1))), θpow(k + 1)))
            R = quo(R - scale(c0, D1), lin0)
            Dsf = D1
        end
        (iszero(R) || degree(Dsf) == 0) && continue
        lg_simple_poles!(ts, b, T, R, Dsf, α, β, k, θt, vt) || throw(RischNotImplemented("step LG: poles"))
    end
    s0 = s[1]
    if !iszero(s0)
        F0 = risch_integrate(xt(s0), x; build = build, lift = lift, verify = verify)
        F0 isa IntegralWithRootSums && throw(RischNotImplemented("step LG: a RootSum"))
        push!(ts, F0)
    end
    isempty(ts) ? b.lift(0) : length(ts) == 1 ? ts[1] : mk(b, :+, ts...)
end

cfromQ_frac(C, k) = frac(UPoly{C}(C[cfromQ(C, Q(k))]))

# Σ over the roots c of D (simple, K = α c + β ≠ 0) of ρ_c [θᵏ log(1 - v/K) + k Σₗ (-1)ˡ (k-1)!/(k-1-l)! θ^(k-1-l) Li_{l+2}(v/K)]
function lg_simple_poles!(ts, b::Builder, T::Tower, R::UPoly{C}, Dsf::UPoly{C}, α, β, k::Int, θt, vt) where {C}
    P = UPoly{C}
    dD = deriv(Dsf)
    θpow(j) = j == 0 ? nothing : j == 1 ? θt : mk(b, :^, θt, b.lift(j))
    mul(t, u) = t === nothing ? u : u === nothing ? t : mk(b, :*, t, u)
    function add!(ρt, κt)                               # ρ(c), 1/K as terms (nothing: 1)
        z = mul(vt, κt)
        parts = Any[mul(θpow(k), mk(b, :log, mk(b, :+, b.lift(1), mk(b, :*, b.lift(-1), z))))]
        for l in 0:(k - 1)
            c = k * (isodd(l) ? -1 : 1) * factorial(k - 1) ÷ factorial(k - 1 - l)
            push!(parts, mul(mul(b.lift(c), θpow(k - 1 - l)), mk(b, :polylog, b.lift(l + 2), z)))
        end
        push!(ts, mul(ρt, length(parts) == 1 ? parts[1] : mk(b, :+, parts...)))
    end
    rest = monic(Dsf)
    for c in constant_roots(Dsf)
        lin = P(C[-c, one(C)])
        iszero(rem(rest, lin)) || continue
        rest = quo(rest, lin)
        ρ = peval(R, c) / peval(dD, c)
        iszero(ρ) && continue
        κ = inv(α * c + β)
        add!(isone(ρ) ? nothing : cterm(b, ρ), isone(κ) ? nothing : cterm(b, κ))
    end
    degree(rest) == 0 && return true
    qs = C === Q ? factor_Q(rest) : [rest]
    for q in qs
        n = degree(q)
        (n == 2 || (n == 4 && iszero(q.c[2]) && iszero(q.c[4]))) || return false
        s1, _, g1 = gcdex(rem(dD, q), q)
        s2, _, g2 = gcdex(rem(P(C[β, α]), q), q)
        (degree(g1) == 0 && degree(g2) == 0) || return false
        ρq = rem(scale(inv(g1.c[1]), R * s1), q)
        κq = scale(inv(g2.c[1]), s2)
        cs(p) = Any[(j <= length(p.c) && !iszero(p.c[j])) ? cterm(b, p.c[j]) : nothing for j in 1:n]
        for (ρt, κt) in lg_root_values(b, q, cs(ρq), cs(κq))
            ρt === nothing || add!(ρt, κt)              # (nothing: ρ ≡ 0 mod q)
        end
    end
    true
end

# at each root c of q (θ² + pθ + s, or θ⁴ + pθ² + s): the values Σ aⱼ cʲ, Σ bⱼ cʲ of two coefficient lists (terms)
function lg_root_values(b::Builder, q::UPoly{C}, as, bs) where {C}
    half = inv(cfromQ(C, Q(2)))
    even = degree(q) == 4
    p, s = even ? (q.c[3], q.c[1]) : (q.c[2], q.c[1])
    sqt = px_sqrt(b, p * p * half * half - s)
    out = Any[]
    for σ in (1, -1)
        v = px_add(b, iszero(p) ? nothing : cterm(b, -p * half), σ == 1 ? sqt : mk(b, :*, b.lift(-1), sqt))
        for r in (even ? (mk(b, :sqrt, v), mk(b, :*, b.lift(-1), mk(b, :sqrt, v))) : (v,))
            push!(out, (px_at(b, as, r, v), px_at(b, bs, r, v)))
        end
    end
    out
end

# v = (p x + q)/(r x + s) not linear (log(e ((a + b x)/(c + d x))ⁿ), samples 1216, 1218, 1230): with w = v, x playing w,
#   x ↦ (q - s w)/(r w - p),   dx ↦ (s p - r q)/(r w - p)² dx,
# the logarithm's argument is linear in w; the integral by the usual route (then this step), and w ↦ v.
function log_powers_mobius(f, x, T::Tower, v, build, lift, verify)
    LG_MOBIUS[] && return nothing
    xk = string(x)
    C = ctype(T)
    P = UPoly{C}
    co(pl, k) = k + 1 <= length(pl.c) ? pl.c[k + 1] : zero(C)
    p, q, r, s = co(v.num, 1), co(v.num, 0), co(v.den, 1), co(v.den, 0)
    iszero(s * p - r * q) && return nothing
    bd = Builder(build === nothing ? auto_build(f, x) : build, lift === nothing ? auto_lift(f, x) : lift, x, T.consts)
    den = P(C[-p, r])
    Xt = frac_term(bd, frac(P(C[q, -s]), den))
    Jt = frac_term(bd, frac(P(C[s * p - r * q]), den * den))
    sub(t) = (safe_iscall(t) && !isempty(arguments(t))) ? term_rebuild(bd, t, Any[sub(a) for a in arguments(t)]) :
             string(t) == xk ? Xt : t
    g = mk(bd, :*, sub(f), Jt)
    LG_MOBIUS[] = true
    G = try
        risch_integrate(g, x; build = build, lift = lift, verify = verify)
    catch e
        (e isa RischNotImplemented || e isa NotElementary) || rethrow()
        nothing
    finally
        LG_MOBIUS[] = false
    end
    (G === nothing || G isa IntegralWithRootSums) && return nothing
    vt = tower_to_term(bd, T, v)
    back(t) = (safe_iscall(t) && !isempty(arguments(t))) ? term_rebuild(bd, t, Any[back(a) for a in arguments(t)]) :
              string(t) == xk ? vt : t
    Gb = back(G)
    (verify && !numeric_antiderivative(f, Gb, xk; pz = true)) && return nothing
    Gb
end

# log(e Uⁿ/Vⁿ) ↦ log(e (U/V)ⁿ) for a symbolic exponent n shared by several factors (equal where U, V > 0, the real
# integrand); nothing when no logarithm has such factors
function combine_log_powers(f, x, xk::String, build, lift)
    @nospecialize f x
    bd = Builder(build === nothing ? auto_build(f, x) : build, lift === nothing ? auto_lift(f, x) : lift, x)
    changed = false
    function factors!(out, t, sg)
        if safe_iscall(t) && !isempty(arguments(t))
            n, args = opname(operation(t)), arguments(t)
            n === :* && return foreach(a -> factors!(out, a, sg), args)
            (n === :/ && length(args) == 2) && return (factors!(out, args[1], sg); factors!(out, args[2], -sg))
            if n === :^ && length(args) == 2 && !has_x(args[2], xk) && leaf_rational(args[2]) === nothing && has_x(args[1], xk)
                return push!(out, (args[1], args[2], sg))
            end
        end
        push!(out, (t, nothing, sg))
    end
    function rw(t)
        (safe_iscall(t) && !isempty(arguments(t))) || return t
        args = Any[rw(a) for a in arguments(t)]
        if opname(operation(t)) === :log && length(args) == 1
            fs = Any[]
            factors!(fs, args[1], 1)
            groups = Dict{String,Vector{Any}}()
            for fc in fs
                fc[2] === nothing || push!(get!(groups, string(fc[2]), Any[]), fc)
            end
            if any(g -> length(g) >= 2, values(groups))
                nums, dens = Any[], Any[]
                for fc in fs
                    (fc[2] !== nothing && length(groups[string(fc[2])]) >= 2) && continue
                    term = fc[2] === nothing ? fc[1] : mk(bd, :^, fc[1], fc[2])
                    push!(fc[3] > 0 ? nums : dens, term)
                end
                for g in values(groups)
                    length(g) >= 2 || continue
                    nb = Any[fc[1] for fc in g if fc[3] > 0]
                    db = Any[fc[1] for fc in g if fc[3] < 0]
                    prod(ts) = isempty(ts) ? bd.lift(1) : length(ts) == 1 ? ts[1] : mk(bd, :*, ts...)
                    base = isempty(db) ? prod(nb) : mk(bd, :/, prod(nb), prod(db))
                    push!(nums, mk(bd, :^, base, g[1][2]))
                end
                changed = true
                a = isempty(nums) ? bd.lift(1) : length(nums) == 1 ? nums[1] : mk(bd, :*, nums...)
                isempty(dens) || (a = mk(bd, :/, a, length(dens) == 1 ? dens[1] : mk(bd, :*, dens...)))
                return mk(bd, :log, a)
            end
        end
        term_rebuild(bd, t, args)
    end
    g = rw(f)
    changed ? g : nothing
end
