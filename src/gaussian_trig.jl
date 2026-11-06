# ---------------------------------------------------------------------------
# Step GT: a Gaussian with trigonometric factors, sin(k x) e^(-x²) (SymPy #21362, #21041)
#
# f = Σ c xⁿ e^L, L = α x² + β x + δ with α ∈ ℚ, β, δ ∈ ℚ(i) and c ∈ ℚ(i): sin, cos (sinh, cosh) of linear
# arguments split into e^(±iu) (e^(±u)), times polynomials and exp of quadratics, all with numeric coefficients,
# times x-free factors. Not elementary for α ≠ 0 (the Risch route says so); each term by
#   x^(m+1) e^L = [(xᵐ e^L)′ - m x^(m-1) e^L - β xᵐ e^L]/(2α),
#   ∫ e^L = e^κ √π/(2√-α) erf(√-α (x + h))  (erfi for α > 0),  h = β/(2α), κ = δ - β²/(4α),
# an erf of a complex shift erf(x - i k/2) for sin(k x) e^(-x²) (erf(x - 1) for e^(-x² + 2x) as before). The
# elementary part is written with e^(Re L)·(cos, sin)(Im L), where the imaginary parts of conjugate terms cancel.
# The answer is checked numerically (complex erf). Nothing when f is not of this form or has no α ≠ 0.
# ---------------------------------------------------------------------------
const CQ = Complex{Q}
const GTKey = Tuple{Int,Q,CQ,CQ}                       # (n, α, β, δ) for xⁿ e^(α x² + β x + δ)

function gt_parse(t, xk::String)
    D = Dict{GTKey,CQ}
    k0 = (0, Q(0), CQ(0), CQ(0))
    addto!(d, k, c) = (iszero(c) || (d[k] = get(d, k, CQ(0)) + c); d)
    function mul(a, b)
        d = D()
        for (ka, ca) in a, (kb, cb) in b
            addto!(d, (ka[1] + kb[1], ka[2] + kb[2], ka[3] + kb[3], ka[4] + kb[4]), ca * cb)
        end
        filter!(p -> !iszero(p[2]), d)
    end
    # a polynomial of degree ≤ 2 (no exponentials): (c₀, c₁, c₂), else nothing
    function quad(d)
        cs = CQ[0, 0, 0]
        for (k, c) in d
            (k[1] <= 2 && iszero(k[2]) && iszero(k[3]) && iszero(k[4])) || return nothing
            cs[k[1] + 1] += c
        end
        cs
    end
    function expo(u)                                   # e^u, u quadratic
        cs = quad(u)
        (cs === nothing || !iszero(imag(cs[3]))) && return nothing
        D(GTKey((0, real(cs[3]), cs[2], cs[1])) => CQ(1))
    end
    function pr(t)
        if !safe_iscall(t) || isempty(arguments(t))
            string(t) == xk && return D(GTKey((1, Q(0), CQ(0), CQ(0))) => CQ(1))
            is_imag_unit(t) && return D(k0 => CQ(0, 1))
            r = leaf_rational(t)
            r !== nothing && return iszero(r) ? D() : D(k0 => CQ(r))
            g = leaf_gaussian(t)
            g !== nothing && return iszero(g) ? D() : D(k0 => CQ(g))
            return nothing
        end
        is_imag_unit(t) && return D(k0 => CQ(0, 1))
        n, args = opname(operation(t)), arguments(t)
        if n === :^ && length(args) == 2 && is_e_const(args[1])    # ℯ^u (SymJ's exp)
            u = pr(args[2])
            return u === nothing ? nothing : expo(u)
        end
        ps = Any[pr(a) for a in args]
        any(isnothing, ps) && return nothing
        if n === :+
            d = D()
            for p in ps, (k, c) in p
                addto!(d, k, c)
            end
            return filter!(p -> !iszero(p[2]), d)
        elseif n === :- && length(ps) == 1
            return D(k => -c for (k, c) in ps[1])
        elseif n === :- && length(ps) == 2
            d = copy(ps[1])
            for (k, c) in ps[2]
                addto!(d, k, -c)
            end
            return filter!(p -> !iszero(p[2]), d)
        elseif n === :*
            return foldl(mul, ps; init = D(k0 => CQ(1)))
        elseif n === :/ && length(ps) == 2
            # a divisor c e^δ only
            (length(ps[2]) == 1 && (k = first(keys(ps[2])); k[1] == 0 && iszero(k[2]) && iszero(k[3]))) || return nothing
            k, c = first(ps[2])
            return mul(ps[1], D(GTKey((0, Q(0), CQ(0), -k[4])) => inv(c)))
        elseif n === :^ && length(ps) == 2
            p = leaf_rational(args[2])
            (p !== nothing && isone(denominator(p)) && 0 <= p <= 12) || return nothing
            return foldl(mul, fill(ps[1], Int(p)); init = D(k0 => CQ(1)))
        elseif n === :exp && length(ps) == 1
            return expo(ps[1])
        elseif n in (:sin, :cos, :sinh, :cosh) && length(ps) == 1
            cs = quad(ps[1])
            (cs === nothing || !iszero(cs[3]) || !iszero(imag(cs[1])) || !iszero(imag(cs[2]))) && return nothing
            w = n in (:sin, :cos) ? CQ(0, 1) : CQ(1)         # e^(±w u)
            kp = GTKey((0, Q(0), w * cs[2], w * cs[1]))
            km = GTKey((0, Q(0), -w * cs[2], -w * cs[1]))
            half = CQ(1 // 2)
            n === :cos && return D(kp => half, km => half)
            n === :cosh && return D(kp => half, km => half)
            n === :sinh && return D(kp => half, km => -half)
            return D(kp => half / CQ(0, 1), km => -half / CQ(0, 1))   # sin u = (e^(iu) - e^(-iu))/(2i)
        end
        nothing
    end
    pr(t)
end

function integrate_gaussian_trig(f, x; build = nothing, lift = nothing, verify::Bool = true)
    @nospecialize f x
    xk = string(x)
    # x-free factors that are not numbers (1/√(2π), parameters) stay outside
    K, rest = Any[], Any[]
    for (b, e) in product_factors!(Any[], f, 1)
        (!has_x(b, xk) && gt_parse(b, xk) === nothing) ? push!(K, (b, e)) : push!(rest, (b, e))
    end
    bd = Builder(build === nothing ? auto_build(f, x) : build, lift === nothing ? auto_lift(f, x) : lift, x)
    pw(b, e) = e == 1 ? b : mk(bd, :^, b, bd.lift(e))
    isempty(rest) && return nothing
    g = length(rest) == 1 ? pw(rest[1]...) : mk(bd, :*, (pw(b, e) for (b, e) in rest)...)
    d = gt_parse(g, xk)
    (d === nothing || isempty(d) || length(d) > 200 || all(k -> iszero(k[2]), keys(d))) && return nothing
    # the integral as Σ c xᵏ e^L (elementary) + Σ c ∫ e^L (erf terms)
    el = Dict{GTKey,CQ}()
    ef = Dict{Tuple{Q,CQ,CQ},CQ}()
    addto!(dd, k, c) = (iszero(c) || (dd[k] = get(dd, k, CQ(0)) + c))
    for ((n, α, β, δ), c) in d
        if iszero(α) && iszero(β)
            addto!(el, (n + 1, α, β, δ), c / (n + 1))
        elseif iszero(α)                               # Iₘ = xᵐ e^L/β - (m/β) Iₘ₋₁
            cm = c
            for m in n:-1:0
                addto!(el, (m, α, β, δ), cm / β)
                cm = -cm * m / β
            end
        else
            # Iₘ = Pₘ(x) e^L + Kₘ ∫ e^L: I₀ = (0, 1), I₁ = (1/(2α), -β/(2α)), Iₘ₊₁ = xᵐe^L/(2α) - m Iₘ₋₁/(2α) - β Iₘ/(2α)
            Ps = Vector{Vector{CQ}}(undef, n + 1)
            Ks = Vector{CQ}(undef, n + 1)
            Ps[1], Ks[1] = CQ[], CQ(1)
            tα = 2α
            for m in 0:(n - 1)
                P = zeros(CQ, m + 1)
                P[m + 1] += 1 / tα
                Km = -β * Ks[m + 1] / tα
                for (j, cj) in enumerate(Ps[m + 1])
                    P[j] -= β * cj / tα
                end
                if m >= 1
                    Km -= m * Ks[m] / tα
                    for (j, cj) in enumerate(Ps[m])
                        P[j] -= m * cj / tα
                    end
                end
                Ps[m + 2], Ks[m + 2] = P, Km
            end
            for (j, cj) in enumerate(Ps[n + 1])
                addto!(el, (j - 1, α, β, δ), c * cj)
            end
            addto!(ef, (α, β, δ), c * Ks[n + 1])
        end
    end
    X = bd.x
    I_ = bd.lift(im)
    num(r::Q) = cterm(bd, r)
    cnum(c::CQ) = iszero(imag(c)) ? num(real(c)) : iszero(real(c)) ? mk(bd, :*, num(imag(c)), I_) :
                  mk(bd, :+, num(real(c)), mk(bd, :*, num(imag(c)), I_))
    xpow(k) = k == 0 ? nothing : k == 1 ? X : mk(bd, :^, X, bd.lift(k))
    prodt(v) = (v = filter(!isnothing, v); isempty(v) ? bd.lift(1) : length(v) == 1 ? v[1] : mk(bd, :*, v...))
    function lin(a::Q, b::Q, c::Q)                     # a x² + b x + c, or nothing for 0
        ts = Any[]
        iszero(a) || push!(ts, mk(bd, :*, num(a), mk(bd, :^, X, bd.lift(2))))
        iszero(b) || push!(ts, isone(b) ? X : mk(bd, :*, num(b), X))
        iszero(c) || push!(ts, num(c))
        isempty(ts) ? nothing : length(ts) == 1 ? ts[1] : mk(bd, :+, ts...)
    end
    # the elementary part: xᵏ e^(α x² + Re β x + Re δ) (cos φ, sin φ), φ = Im β x + Im δ with Im β > 0 (or = 0, Im δ ≥ 0)
    basis = Dict{Tuple{Int,Q,Q,Q,Q,Q,Symbol},CQ}()
    for ((k, α, β, δ), c) in el
        sb, sd = imag(β), imag(δ)
        s = (sb < 0 || (iszero(sb) && sd < 0)) ? -1 : 1
        key(kind) = (k, α, real(β), real(δ), s * sb, s * sd, kind)
        addto!(basis, key(:cos), c)
        (iszero(sb) && iszero(sd)) || addto!(basis, key(:sin), c * CQ(0, s))   # e^(iφ) = cos φ + i sin φ
    end
    terms = Any[]
    for ((k, α, rb, rd, ib, id, kind), c) in sort!(collect(basis); by = p -> (p[1][1], p[1][7]))
        iszero(c) && continue
        L = lin(α, rb, rd)
        φ = lin(Q(0), ib, id)
        push!(terms, prodt(Any[cnum(c), xpow(k), L === nothing ? nothing : mk(bd, :exp, L),
                               φ === nothing ? nothing : mk(bd, kind, φ)]))
    end
    for ((α, β, δ), c) in sort!(collect(ef); by = p -> (p[1][1], imag(p[1][2]), real(p[1][2])))
        iszero(c) && continue
        κ = δ - β^2 / (4α)
        h = β / (2α)
        a = abs(α)
        sa = isone(a) ? nothing : mk(bd, :sqrt, num(a))
        xh = iszero(h) ? X : mk(bd, :+, X, cnum(h))
        arg = sa === nothing ? xh : mk(bd, :*, sa, xh)
        E = lin(Q(0), Q(0), real(κ))
        ϕ = lin(Q(0), Q(0), imag(κ))
        eκ = Any[E === nothing ? nothing : mk(bd, :exp, E),
                 ϕ === nothing ? nothing : mk(bd, :+, mk(bd, :cos, ϕ), mk(bd, :*, I_, mk(bd, :sin, ϕ)))]
        push!(terms, prodt(Any[cnum(c / 2), eκ..., sa === nothing ? mk(bd, :sqrt, bd.lift(π)) : mk(bd, :/, mk(bd, :sqrt, bd.lift(π)), sa),
                               mk(bd, α < 0 ? :erf : :erfi, arg)]))
    end
    isempty(terms) && return nothing
    G = length(terms) == 1 ? terms[1] : mk(bd, :+, terms...)
    isempty(K) || (G = mk(bd, :*, (pw(b, e) for (b, e) in K)..., G))
    (verify && !numeric_antiderivative(f, G, xk)) && return nothing
    G
end

# step FX: ∫ c g = c ∫ g with c the product of the factors of f free of x (√2 too, which step IT leaves in: it
# is a constant of the field ℚ(√2)), for a refusal of the field. Nothing when f has no such factor or ∫ g is refused.
function integrate_free_factors_out(f, x; build = nothing, lift = nothing, verify::Bool = true)
    @nospecialize f x
    xk = string(x)
    fs = product_factors!(Any[], f, 1)
    K = [(b, e) for (b, e) in fs if !has_x(b, xk) && leaf_rational(b) === nothing]
    rest = [(b, e) for (b, e) in fs if has_x(b, xk) || leaf_rational(b) !== nothing]
    (isempty(K) || !any(((b, _),) -> has_x(b, xk), rest)) && return nothing
    bd = Builder(build === nothing ? auto_build(f, x) : build, lift === nothing ? auto_lift(f, x) : lift, x)
    pw(b, e) = e == 1 ? b : mk(bd, :^, b, bd.lift(e))
    prodt(v) = length(v) == 1 ? pw(v[1]...) : mk(bd, :*, (pw(b, e) for (b, e) in v)...)
    G = try
        risch_integrate(prodt(rest), x; build = build, lift = lift, verify = verify)
    catch e
        (e isa RischNotImplemented || e isa NotElementary) || rethrow()
        return nothing
    end
    c = prodt(K)
    G isa IntegralWithRootSums && return IntegralWithRootSums(mk(bd, :*, c, G.elementary),
                                                             Any[ScaledRootSum(c, rs) for rs in G.rootsums], G.var)
    mk(bd, :*, c, G)
end
