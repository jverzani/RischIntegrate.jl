# ---------------------------------------------------------------------------
# Stage 5c: polynomial × exponential × trigonometric integrands
#
# sin, cos, sinh, cosh and exp of *linear* arguments are rewritten with complex
# exponentials, so the integrand becomes  F = Σ_λ P_λ(x) e^{λx},  P_λ ∈ ℚ(i)[x],
# λ ∈ ℚ(i) (this is the Risch algorithm in the exponential tower with the constant
# field ℚ(i), where every term is integrable: ∫ P e^{λx} = e^{λx} Σ_k (-1)^k P^(k)/λ^(k+1)).
# The antiderivative is verified exactly (G' = F in this representation) and then
# folded back to real form: conjugate pairs λ = a ± ib give e^{ax}(A cos bx + B sin bx).
# Integrands outside this class (sin(x)/x, 1/(2 + cos x), tan, ...) need the full
# ℚ(i)-tower and raise RischNotImplemented (planned: Stage 5c-ii).
# ---------------------------------------------------------------------------
const QIX = UPoly{QI}
const EP = Dict{QI,QIX}                 # λ => P  meaning  Σ P(x) e^{λx}
const QI0 = QI(Q(0), Q(0))
qi(c::Q) = QI(c, Q(0))

function ep_put!(r::EP, λ::QI, P::QIX)
    S = haskey(r, λ) ? r[λ] + P : P
    iszero(S) ? delete!(r, λ) : (r[λ] = S)
    r
end
function ep_add(f::EP, g::EP)
    r = copy(f)
    for (λ, P) in g
        ep_put!(r, λ, P)
    end
    r
end
function ep_mul(f::EP, g::EP)
    r = EP()
    for (λ1, P1) in f, (λ2, P2) in g
        ep_put!(r, λ1 + λ2, P1 * P2)
    end
    r
end
ep_scale(f::EP, c::QI) = (r = EP(); for (λ, P) in f; ep_put!(r, λ, scale(c, P)); end; r)
ep_const(c::QI) = iszero(c) ? EP() : EP(QI0 => QIX(QI[c]))
ep_one() = ep_const(qi(Q(1)))
function ep_pow(f::EP, n::Int)
    r = ep_one()
    for _ in 1:n
        r = ep_mul(r, f)
    end
    r
end
ep_deriv(f::EP) = (r = EP(); for (λ, P) in f; ep_put!(r, λ, deriv(P) + scale(λ, P)); end; r)

# constant value of an EP (frequency 0, degree 0), or nothing
function ep_constant(f::EP)
    isempty(f) && return QI0
    (length(f) == 1 && haskey(f, QI0) && degree(f[QI0]) <= 0) ? f[QI0].c[1] : nothing
end

# u = c x (linear, no constant term) -> c
function ep_linear(u::EP)
    isempty(u) && return QI0
    (length(u) == 1 && haskey(u, QI0)) || throw(RischNotImplemented(
        "the argument of exp/sin/cos must be a linear function of x for this class of integrands"))
    P = u[QI0]
    degree(P) <= 1 || throw(RischNotImplemented(
        "exp/sin/cos of a nonlinear argument: not of the form polynomial × exponential × trig (Stage 5c-ii)"))
    iszero(P.c[1]) || throw(RischNotImplemented(
        "an argument with a nonzero constant term brings in e^c, sin c or cos c as new constants (Stage 5d)"))
    length(P.c) == 2 ? P.c[2] : QI0
end
ep_expc(c::QI) = iszero(c) ? ep_one() : EP(c => QIX(QI[qi(Q(1))]))
const QI_I = QI(Q(0), Q(1))

function parse_ep(t, xk::String)::EP
    if safe_iscall(t) && !isempty(arguments(t))
        args = arguments(t)
        n = opname(operation(t))
        if n === :^ && length(args) == 2 && is_e_const(args[1])
            return ep_expc(ep_linear(parse_ep(args[2], xk)))
        end
        a = EP[parse_ep(u, xk) for u in args]
        two = qi(Q(2))
        if n === :+
            return foldl(ep_add, a; init = EP())
        elseif n === :-
            length(a) == 1 && return ep_scale(a[1], qi(Q(-1)))
            return ep_add(a[1], ep_scale(foldl(ep_add, a[2:end]; init = EP()), qi(Q(-1))))
        elseif n === :*
            return foldl(ep_mul, a; init = ep_one())
        elseif (n === :/ && length(a) == 2) || (n === :inv && length(a) == 1)
            den = ep_constant(a[end])
            (den === nothing || iszero(den)) && throw(RischNotImplemented(
                "division by a non-constant is outside polynomial × exponential × trig (Stage 5c-ii)"))
            return ep_scale(n === :inv ? ep_one() : a[1], inv(den))
        elseif n === :^ && length(a) == 2
            k = ep_constant(a[2])
            (k !== nothing && iszero(k.im) && isone(denominator(k.re)) && k.re >= 0 && k.re <= 10_000) ||
                throw(RischNotImplemented("only nonnegative integer powers are supported here"))
            return ep_pow(a[1], Int(numerator(k.re)))
        elseif n === :exp && length(a) == 1
            return ep_expc(ep_linear(a[1]))
        elseif n in (:sin, :cos) && length(a) == 1
            c = ep_linear(a[1])
            ep, em = ep_expc(QI_I * c), ep_expc(-(QI_I * c))
            n === :cos && return ep_scale(ep_add(ep, em), inv(two))
            return ep_scale(ep_add(ep, ep_scale(em, qi(Q(-1)))), inv(QI(Q(0), Q(2))))
        elseif n in (:sinh, :cosh) && length(a) == 1
            c = ep_linear(a[1])
            ep, em = ep_expc(c), ep_expc(-c)
            n === :cosh && return ep_scale(ep_add(ep, em), inv(two))
            return ep_scale(ep_add(ep, ep_scale(em, qi(Q(-1)))), inv(two))
        else
            throw(RischNotImplemented(
                "`$n` is outside polynomial × exponential × trig; the full ℚ(i)-tower is planned (Stage 5c-ii)"))
        end
    end
    string(t) == xk && return EP(QI0 => QIX(QI[QI0, qi(Q(1))]))
    r = leaf_rational(t)
    r !== nothing && return ep_const(qi(r))
    is_e_const(t) && throw(RischNotImplemented("the constant e (Stage 5d)"))
    throw(RischNotImplemented("symbol `$t` is not the integration variable"))
end

function ep_integrate(f::EP)
    r = EP()
    for (λ, P) in f
        if iszero(λ)
            c = QI[i == 1 ? QI0 : P.c[i - 1] * inv(qi(Q(i - 1))) for i in 1:(length(P.c) + 1)]
            ep_put!(r, λ, QIX(c))
        else
            il = inv(λ)
            acc, d, c = zero(QIX), P, il
            while !iszero(d)
                acc = acc + scale(c, d)
                d = deriv(d)
                c = -(c * il)
            end
            ep_put!(r, λ, acc)
        end
    end
    r
end

has_trig(t) = safe_iscall(t) && !isempty(arguments(t)) &&
              (opname(operation(t)) in (:sin, :cos, :tan, :cot, :sec, :csc) || any(has_trig, arguments(t)))

conj_poly(P::QIX) = QIX(QI[QI(c.re, -c.im) for c in P.c])

function ep_to_term(b::Builder, G::EP)
    ts = Any[]
    expfac(a::Q) = iszero(a) ? nothing :
        mk(b, :exp, isone(a) ? b.x : mk(b, :*, b.lift(num(a)), b.x))
    function times(p::CX, fac)
        iszero(p) && return nothing
        parts = Any[]
        isone(p) || push!(parts, poly_term(b, p))
        fac === nothing || push!(parts, fac)
        isempty(parts) ? b.lift(1) : length(parts) == 1 ? parts[1] : mk(b, :*, parts...)
    end
    for λ in sort(collect(keys(G)); by = z -> (z.re, z.im))
        P = G[λ]
        if iszero(λ.im)
            all(iszero(c.im) for c in P.c) || throw(RischError("non-real coefficient for a real frequency"))
            t = times(CX(Q[c.re for c in P.c]), expfac(λ.re))
            t === nothing || push!(ts, t)
        elseif λ.im > 0
            get(G, QI(λ.re, -λ.im), nothing) == conj_poly(P) ||
                throw(RischError("antiderivative is not conjugate-symmetric"))
            ea = expfac(λ.re)
            ωx = isone(λ.im) ? b.x : mk(b, :*, b.lift(num(λ.im)), b.x)
            for (p, fn) in ((CX(Q[2c.re for c in P.c]), :cos), (CX(Q[-2c.im for c in P.c]), :sin))
                t = times(p, nothing)
                t === nothing && continue
                tr = mk(b, fn, ωx)
                push!(ts, isone(p) ? (ea === nothing ? tr : mk(b, :*, ea, tr)) :
                          (ea === nothing ? mk(b, :*, t, tr) : mk(b, :*, t, ea, tr)))
            end
        end
    end
    isempty(ts) && return b.lift(0)
    length(ts) == 1 ? ts[1] : mk(b, :+, ts...)
end

function integrate_trig(f, x; build = nothing, lift = nothing, verify::Bool = true)
    F = parse_ep(f, string(x))
    G = ep_integrate(F)
    verify && ep_deriv(G) != F && throw(RischError("internal check failed (trigonometric integral)"))
    bd = Builder(build === nothing ? auto_build(f, x) : build,
                 lift === nothing ? auto_lift(f, x) : lift, x)
    ep_to_term(bd, G)
end
