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
    (length(T.levels) == 1 && T.levels[1].kind === :log && levelof(T, el) == 1) || return nothing
    C = ctype(T)
    arg = T.levels[1].arg                               # v ∈ C(x)
    (degree(arg.den) == 0 && degree(arg.num) == 1) || return nothing
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
