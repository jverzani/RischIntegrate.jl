# ---------------------------------------------------------------------------
# Step CL: ∫ xᵖ·R(sin kx, cos kx) by parts, with Clausen functions (∫ x tan x, ∫ x sin³x/cos³x, ∫ x³ tan⁴ x).
# In the ℚ(i) tower, θ = e^(ikx), f = Σ_p xᵖ R_p(θ) + S(θ); S is integrated as usual, and
#   ∫ xᵖ R = Σ_{j=0..p} (-1)ʲ p!/(p-j)! x^(p-j) G_{j+1},   G₁ = ∫ R, G_{j+1} = ∫ G_j.
# Each G_j is real: Re V + Σ c Cl_m(kx - ψπ) + a polynomial in x (coefficients in ℚ[π, log ℚ]). The
# rational part integrates by Risch, ∫ V = v + Σ c log W(θ); each W is lc·Π (θ - r)^m with roots r = 0 or
# on the unit circle in ℚ(i) (±1, ±i), r = e^(iψπ), φ = kx - ψπ; then log(θ - r) = log(-r) + log(1 - θ/r)
# and, on 0 < φ < 2π,
#   log(1 - e^(iφ)) = -Cl₁(φ) + i (φ - π)/2,   log(-r) = i arg(-r),   log θ = i k x,
# with Cl₁(φ) = -log|2 sin(φ/2)| printed as -½ log(2 - 2 cos φ). The real part of each, Re v + Σ Re(c ·),
# differentiates to the integrand wherever it is smooth (the imaginary part is constant), and the Clausen
# terms integrate as ∫ Cl_m(φ) dx = ±Cl_{m+1}(φ)/k (+ for odd m), so every G_j has this form.
# A root r = R u off the axes (u = e^(iβ) ∈ ℚ(i), R ∈ ℚ, β not a rational multiple of π) is the same with
# φ = kx - β: only the constants differ, and constants cancel in Σ (-1)ʲ p!/(p-j)! x^(p-j) G_{j+1} (a constant
# C in G_n adds C x^(p-n+1) p!/(p-n+1)! Σᵢ (-1)ⁱ⁺ⁿ⁻¹ binom(p-n+1, i) = 0 for n ≤ p), so they are left out.
# A root off the unit circle, |r| = R ≠ 1, gives Re(d Li₁(ρ e^(iφ))) with ρ < 1:
#   R > 1: log(θ - r) = log(-r) + log(1 - θ/r),  θ/r = e^(iφ)/R,
#   R < 1: log(θ - r) = i k x + log(1 - r/θ),     r/θ = R e^(-iφ), and Re(c L̄) = Re(c̄ L),
# with log(1 - z) = -Li₁(z), and ∫ Re(d Liₘ(ρ e^(iφ))) dx = Re(-i d Li_{m+1}(ρ e^(iφ)))/k. They print
# with repolylog(m, ρ, φ) = Re Liₘ(ρ e^(iφ)) and impolylog(m, ρ, φ) = Im Liₘ(ρ e^(iφ)) (elementary for m = 1).
# ---------------------------------------------------------------------------
"""
    clausen(n, φ)

The Clausen function Cl_n(φ): Σₖ cos(kφ)/kⁿ for odd n, Σₖ sin(kφ)/kⁿ for even n (the real resp. imaginary
part of Liₙ(e^{iφ})), with Cl₁(φ) = -log|2 sin(φ/2)|. Then Cl′_{n+1} = Cl_n for odd n and -Cl_n for even n.
RischIntegrate uses it in answers such as ∫ x³ tan x dx; see also [`clausen2`](@ref).
"""
clausen(n::Integer, φ::Real) = n == 1 ? -log(abs(2 * sin(φ / 2))) :
                               (z = PolyLog.li(n, cis(φ)); isodd(n) ? real(z) : imag(z))
"""
    clausen2(φ)

Clausen's function Cl₂(φ) = Im Li₂(e^{iφ}) = Σₙ sin(nφ)/n², with Cl₂′(φ) = -log|2 sin(φ/2)|. RischIntegrate
uses it in answers such as ∫ x tan x dx.
"""
clausen2(φ::Real) = imag(li2(cis(φ)))
OPS[:Cl2] = clausen2
OPS[:Cl] = clausen
"""
    repolylog(n, ρ, φ)

Re Liₙ(ρ e^{iφ}) for real ρ (principal branch), = Σₖ ρᵏ cos(kφ)/kⁿ for |ρ| ≤ 1. RischIntegrate uses it, with
[`impolylog`](@ref), in answers such as ∫ x/(5 + 4 cos x) dx; at ρ = 1 these are the Clausen functions
([`clausen`](@ref)), and repolylog(n, y, 0) = Liₙ(y) for y ≤ 1 (∫ log(x) log(1 + x)/x dx).
"""
repolylog(n::Integer, ρ::Real, φ::Real) = real(PolyLog.li(n, ρ * cis(φ)))
"""
    impolylog(n, ρ, φ)

Im Liₙ(ρ e^{iφ}) for real ρ (principal branch), = Σₖ ρᵏ sin(kφ)/kⁿ for |ρ| ≤ 1; see [`repolylog`](@ref).
impolylog(n, x, π/2) = Im Liₙ(i x) is the inverse tangent integral Tiₙ(x) (∫ atan(x) log(x)/x dx).
"""
impolylog(n::Integer, ρ::Real, φ::Real) = imag(PolyLog.li(n, ρ * cis(φ)))
# (a whole n as a float: the numeric evaluation of an answer kept as an Expr)
clausen(n::Real, φ::Real) = clausen(Int(n), φ)
repolylog(n::Real, ρ::Real, φ::Real) = repolylog(Int(n), ρ, φ)
impolylog(n::Real, ρ::Real, φ::Real) = impolylog(Int(n), ρ, φ)
OPS[:ReLi] = repolylog
OPS[:ImLi] = impolylog

const CK = Dict{Tuple{Int,Q},Q}                         # Σ q πʲ log L, keyed (j, L) (L = 1: q πʲ)
addck!(d::CK, key, q) = (iszero(q) || (d[key] = get(d, key, Q(0)) + q); d)

# an iterated antiderivative: Re V + Σ c Cl_m(kx - β) + Σ Re(d Li_m(ρ e^(i(kx - β)))) + Σ_d P[d+1] x^d, u = e^(iβ)
struct ClausenSum
    V::Any
    cl::Dict{Tuple{Int,QI},Q}                           # (m, u) => c
    li::Dict{Tuple{Int,Q,QI},QI}                        # (m, ρ, u) => d
    P::Vector{CK}
end

const MAX_X_POWER = 6

function try_x_trig(f, x; build = nothing, lift = nothing, verify::Bool = true)
    @nospecialize f x
    g = x_trig(f, x, build, lift, verify, false)
    g === nothing ? x_trig(f, x, build, lift, verify, true) : g
end

# in_power: integrate a function of θ^g in y = g x (tried second: in θ the answers keep their usual form)
function x_trig(f, x, build, lift, verify::Bool, in_power::Bool)
    @nospecialize f x
    xk = string(x)
    T, el = try
        build_tower(f, xk)
    catch e
        (e isa RischNotImplemented || e isa RischError) && return nothing
        rethrow()
    end
    C = ctype(T)
    (C === QI && length(T.levels) == 1 && T.levels[1].kind === :exp && levelof(T, el) == 1) || return nothing
    a = T.levels[1].arg
    (isone(a.den) && degree(a.num) == 1 && iszero(a.num.c[1])) || return nothing
    I = cimag(C)
    kr = to_real(a.num.c[2] * inv(I))
    kr isa Q || return nothing
    k = kr                                              # θ = e^(ikx)
    # el = Σ xᵖ R_p: the θ-coefficients of the numerator are polynomials in x, the denominator's constant
    cst(c) = const_value(T, c)
    Dc = [cst(c) for c in el.den.c]
    any(isnothing, Dc) && return nothing
    Rc = [C[] for _ in 0:MAX_X_POWER]                   # Rc[p + 1]: θ-coefficients of R_p
    for c in el.num.c                                   # c ∈ K0 = ℚ(i)(x)
        degree(c.den) == 0 || return nothing
        degree(c.num) <= MAX_X_POWER || return nothing
        d0 = c.den.c[1]
        for p in 0:MAX_X_POWER
            push!(Rc[p + 1], p < length(c.num.c) ? c.num.c[p + 1] / d0 : zero(C))
        end
    end
    any(p -> !all(iszero, Rc[p + 1]), 1:MAX_X_POWER) || return nothing
    # a function of θ^g only (sin²x: θ = e^(ix), roots ±√3 of θ², rational in θ²): integrate in y = g x, θ_y = θ^g;
    # ∫ xᵖ R(θ^g) dx = g^-(p+1) ∫ yᵖ R(θ_y) dy, and y = g x in the output
    gθ = 0
    for cs in (Dc, Rc...), (i, c) in enumerate(cs)
        iszero(c) || (gθ = gcd(gθ, i - 1))
    end
    in_power && gθ <= 1 && return nothing
    in_power || (gθ = 1)
    if gθ > 1
        Dc = Dc[1:gθ:end]
        Rc = [cs[1:gθ:end] for cs in Rc]
    end
    gθ = max(gθ, 1)
    K0 = T.Ts[1]
    θ = frac(xpoly(K0))
    li(c) = lconst(T, c, 1)
    ev(cs) = foldr((c, acc) -> acc * θ + li(c), cs; init = zero(θ))
    Dθ = ev(Dc)
    kinds = sigma_kinds(T)
    half = inv(cfromQ(C, Q(2)))
    re(v) = (v = liftto(T, v, 1); (v + tconj(T, kinds, v, 1)) * li(half))
    # ∫ V as (Re v, logs), or nothing
    function int_el(V)
        res = try
            integrate_el(T, 1, V)
        catch e
            (e isa NotElementary || e isa RischNotImplemented) && return nothing
            rethrow()
        end
        (isempty(res.atans) && isempty(res.quads)) || return nothing
        res
    end
    # Σ Re(c log W) into the Clausen and Li terms (m = 1) and the polynomial of G; false if a root has |r| ∉ ℚ
    function add_logs!(G::ClausenSum, logs)
        for (c, W0) in logs
            W0 = liftto(T, W0, 1)                       # an element of K₁: a polynomial in θ over K₀
            (W0 isa Frac && degree(W0.den) == 0) || return false
            dW = cst(W0.den.c[1])
            dW === nothing && return false
            Wc = [cst(w) for w in W0.num.c]
            any(isnothing, Wc) && return false
            Wp = UPoly{C}(C[w / dW for w in Wc])
            cr, ci = c.re, c.im
            rest = Wp                                   # roots with multiplicity
            roots = Tuple{QI,Int}[]
            while degree(rest) > 0
                rs = constant_roots(rest)
                isempty(rs) && return false
                r = rs[1]
                m = 0
                lin1 = UPoly{C}(C[-r, one(C)])
                while degree(rest) > 0 && iszero(rem(rest, lin1))
                    rest = quo(rest, lin1)
                    m += 1
                end
                push!(roots, (r, m))
            end
            lcW = lc(Wp)                                # Re(c log lcW) = cr log|lcW| - ci arg(lcW)
            argq = axis_arg(lcW)                        # (a constant: left out off the axes)
            n2 = lcW.re^2 + lcW.im^2
            isone(n2) || addck!(G.P[1], (0, n2), cr / 2)
            argq === nothing || addck!(G.P[1], (1, Q(1)), -ci * argq)
            for (r, m) in roots
                if iszero(r)                            # log θ = i k x: Re(c i k x) = -ci k x
                    addck!(G.P[2], (0, Q(1)), -ci * k * m)
                    continue
                end
                ψ = axis_arg(r)                         # in units of π, ψ ∈ [0, 2); nothing off the axes
                R = rat_sqrt(r.re^2 + r.im^2)           # |r|
                R === nothing && return false
                u = r / cfromQ(C, R)
                if R != 1
                    cq = QI(cr, ci)
                    if R > 1                            # Re(c log(-r)) = cr log R - ci arg(-r) π
                        addck!(G.P[1], (0, R), cr * m)
                        ψ === nothing || addck!(G.P[1], (1, Q(1)), -ci * m * axis_arg(-r))
                        key, d = (1, inv(R), u), -cq
                    else                                # Re(c i k x) = -ci k x
                        addck!(G.P[2], (0, Q(1)), -ci * k * m)
                        key, d = (1, R, u), -cconj(cq)
                    end
                    G.li[key] = get(G.li, key, zero(QI)) + d * m
                    continue
                end
                # Re(c log(θ - r)) = -cr Cl₁(φ) - ci (arg(-r) π + (kx - (ψ + 1)π)/2)
                iszero(cr) || (G.cl[(1, u)] = get(G.cl, (1, u), Q(0)) - cr * m)
                if ψ !== nothing
                    ψ = ψ < 0 ? ψ + 2 : ψ
                    addck!(G.P[1], (1, Q(1)), -ci * m * (axis_arg(-r) - (ψ + 1) / 2))   # arg(-r) ∈ (-1, 1] (× π)
                end
                addck!(G.P[2], (0, Q(1)), -ci * m * k / 2)
            end
        end
        true
    end
    # G₁, …, G_n for R
    function antiderivatives(R, n)
        res = int_el(R)
        res === nothing && return nothing
        G = ClausenSum(re(res.v), Dict{Tuple{Int,QI},Q}(), Dict{Tuple{Int,Q,QI},QI}(), [CK(), CK()])
        add_logs!(G, res.logs) || return nothing
        Gs = [G]
        for _ in 2:n
            P = [CK()]                                  # ∫ Σ P_d x^d = Σ P_d x^(d+1)/(d+1)
            for (d, cd) in enumerate(G.P)
                push!(P, CK(key => q / d for (key, q) in cd))
            end
            push!(P, CK())
            cl = Dict{Tuple{Int,QI},Q}(((m + 1, u) => (isodd(m) ? c : -c) / k) for ((m, u), c) in G.cl)
            lis = Dict{Tuple{Int,Q,QI},QI}(((m + 1, ρ, u) => QI(d.im / k, -d.re / k)) for ((m, ρ, u), d) in G.li)
            V = zero(G.V)
            Gn = ClausenSum(V, cl, lis, P)
            if !iszero(G.V)
                r = int_el(G.V)
                r === nothing && return nothing
                Gn = ClausenSum(re(r.v), cl, lis, P)
                add_logs!(Gn, r.logs) || return nothing
            end
            G = Gn
            push!(Gs, G)
        end
        Gs
    end
    # ∫ Σ_p xᵖ R_p = Σ_p Σ_j (-1)ʲ p!/(p-j)! x^(p-j) G^(p)_{j+1}, collected: rational parts with their powers
    # of x, the Clausen terms with polynomial multipliers, one polynomial
    Vts = Tuple{Q,Int,Any}[]
    CLs = Dict{Tuple{Int,QI},Vector{Q}}()
    LIs = Dict{Tuple{Symbol,Int,Q,QI},Vector{Q}}()      # (:re or :im, m, ρ, u): Re(d L) = dr Re L - di Im L
    Ps = CK[]
    for p in 1:MAX_X_POWER
        all(iszero, Rc[p + 1]) && continue
        Gs = antiderivatives(ev(Rc[p + 1]) / Dθ, p + 1)
        Gs === nothing && return nothing
        for j in 0:p
            coef = Q((-1)^j * factorial(p) ÷ factorial(p - j)) / Q(gθ)^(j + 1)   # g^-(p+1) (g x)^(p-j)
            xp = p - j
            G = Gs[j + 1]
            iszero(G.V) || push!(Vts, (coef, xp, G.V))
            function addM!(D, key, c)
                M = get!(() -> Q[], D, key)
                while length(M) <= xp
                    push!(M, Q(0))
                end
                M[xp + 1] += coef * c
            end
            for (key, c) in G.cl
                addM!(CLs, key, c)
            end
            for ((m, ρ, u), d) in G.li
                iszero(d.re) || addM!(LIs, (:re, m, ρ, u), d.re)
                iszero(d.im) || addM!(LIs, (:im, m, ρ, u), -d.im)
            end
            for (d, cd) in enumerate(G.P)
                while length(Ps) < d + xp
                    push!(Ps, CK())
                end
                for (key, q) in cd
                    addck!(Ps[d + xp], key, coef * q * Q(gθ)^(d - 1))
                end
            end
        end
    end
    bd = Builder(build === nothing ? auto_build(f, x) : build, lift === nothing ? auto_lift(f, x) : lift, x, T.consts)
    πt = bd.lift(π)
    kxt = isone(k * gθ) ? bd.x : mk(bd, :*, cterm(bd, k * gθ), bd.x)
    bdy = gθ == 1 ? bd : Builder(bd.build, bd.lift, mk(bd, :*, bd.lift(gθ), bd.x), bd.consts)   # x as y = g x
    xpow(d) = d == 1 ? bd.x : mk(bd, :^, bd.x, bd.lift(d))
    times_x(t, d) = d == 0 ? t : mk(bd, :*, xpow(d), t)
    sc(c, t) = isone(c) ? t : mk(bd, :*, cterm(bd, c), t)
    # (q, polynomial multiplier M(x), base term) as a term
    function mul_poly(M::Vector{Q}, t)
        nz = findall(!iszero, M)
        isempty(nz) && return nothing
        length(nz) == 1 && return sc(M[nz[1]], times_x(t, nz[1] - 1))
        mk(bd, :*, poly_term(bd, UPoly{Q}(M)), t)
    end
    function ck_term(d::CK)
        ts = Any[]
        for key in sort!(collect(keys(d)))
            q = d[key]
            iszero(q) && continue
            j, L = key
            fs = Any[]
            j >= 1 && push!(fs, j == 1 ? πt : mk(bd, :^, πt, bd.lift(j)))
            isone(L) || push!(fs, mk(bd, :log, cterm(bd, L)))
            isempty(fs) && (push!(ts, cterm(bd, q)); continue)
            b = length(fs) == 1 ? fs[1] : mk(bd, :*, fs...)
            push!(ts, sc(q, b))
        end
        isempty(ts) ? nothing : length(ts) == 1 ? ts[1] : mk(bd, :+, ts...)
    end
    terms = Any[]
    for (coef, xp, V) in Vts
        push!(terms, sc(coef, times_x(real_term(bdy, T, kinds, V, 1), xp)))
    end
    ckx, skx = mk(bd, :cos, kxt), mk(bd, :sin, kxt)
    # a + b cos kx + c sin kx
    function trig_lin(a, b, c)
        ts = Any[]
        iszero(a) || push!(ts, cterm(bd, a))
        iszero(b) || push!(ts, isone(b) ? ckx : mk(bd, :*, cterm(bd, b), ckx))
        iszero(c) || push!(ts, isone(c) ? skx : mk(bd, :*, cterm(bd, c), skx))
        length(ts) == 1 ? ts[1] : mk(bd, :+, ts...)
    end
    # φ = kx - β, u = e^(iβ): β = ψπ on an axis, else atan(im/re) (+ π for re < 0)
    function phi_term(u::QI)
        ψ = axis_arg(u)
        if ψ !== nothing
            ψ = ψ < 0 ? ψ + 2 : ψ
            return iszero(ψ) ? kxt : mk(bd, :+, kxt, mk(bd, :*, cterm(bd, -ψ), πt))
        end
        ts = Any[kxt, mk(bd, :*, bd.lift(-1), mk(bd, :atan, cterm(bd, u.im / u.re)))]
        u.re < 0 && push!(ts, mk(bd, :*, bd.lift(-1), πt))
        mk(bd, :+, ts...)
    end
    # cos φ = re cos kx + im sin kx, sin φ = re sin kx - im cos kx
    for key in sort!(collect(keys(CLs)); by = string)
        m, u = key
        M = CLs[key]
        if m == 1                                       # Cl₁(φ) = -½ log(2 - 2 cos φ)
            base = mk(bd, :log, trig_lin(Q(2), -2u.re, -2u.im))
            M = -M / 2
        else
            φt = phi_term(u)
            base = m == 2 ? mk(bd, :Cl2, φt) : mk(bd, :Cl, bd.lift(m), φt)
        end
        t = mul_poly(M, base)
        t === nothing || push!(terms, t)
    end
    for key in sort!(collect(keys(LIs)); by = string)
        part, m, ρ, u = key
        M = LIs[key]
        if m == 1
            if part === :re                             # Re Li₁ = -½ log(1 - 2ρ cos φ + ρ²)
                base = mk(bd, :log, trig_lin(1 + ρ^2, -2ρ * u.re, -2ρ * u.im))
                M = -M / 2
            else                                        # Im Li₁ = atan(ρ sin φ/(1 - ρ cos φ))
                base = mk(bd, :atan, mk(bd, :/, trig_lin(Q(0), -ρ * u.im, ρ * u.re), trig_lin(Q(1), -ρ * u.re, -ρ * u.im)))
            end
        else
            base = mk(bd, part === :re ? :ReLi : :ImLi, bd.lift(m), cterm(bd, ρ), phi_term(u))
        end
        t = mul_poly(M, base)
        t === nothing || push!(terms, t)
    end
    for (d, cd) in enumerate(Ps)
        t = ck_term(cd)
        t === nothing || push!(terms, times_x(t, d - 1))
    end
    F = isempty(terms) ? bd.lift(0) : length(terms) == 1 ? terms[1] : mk(bd, :+, terms...)
    if !all(iszero, Rc[1])
        St = real_term(bdy, T, kinds, ev(Rc[1]) / Dθ, 1)
        FS = risch_integrate(St, x; build = build, lift = lift, verify = verify)
        FS isa IntegralWithRootSums && return nothing
        F = mk(bd, :+, F, FS)
    end
    F
end

# arg(z)/π for z on an axis of ℚ(i) (0, 1, 1/2, -1/2), else nothing
function axis_arg(z::QI)
    iszero(z.im) && return z.re > 0 ? Q(0) : Q(1)
    iszero(z.re) && return z.im > 0 ? Q(1, 2) : Q(-1, 2)
    nothing
end
