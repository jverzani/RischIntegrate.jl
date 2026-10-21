# ---------------------------------------------------------------------------
# Phase 6, H3: incomplete gamma answers. For b < 0 and s ∉ ℤ (rational, or a symbolic exponent):
#   ∫ xˢ e^(bx + d) dx = -e^d (-b)^(-s-1) Γ(s + 1, -bx)      (x > 0; d/dw Γ(s+1, w) = -wˢ e^(-w))
# Tried when the Risch machinery decides NotElementary for a sum of terms C xˢ exp(bx + d); terms with an
# integer s are integrated as usual. The Γ term is a symbolic `gamma(s + 1, -bx)` call when the term type
# can build one (Expr, …), else a `GammaTerm` evaluated numerically (numeric s only), as for ₂F₁.
# ---------------------------------------------------------------------------
using SpecialFunctions: gamma

"""
    GammaTerm

`-c e^d (-b)^(-s-1) Γ(s + 1, -b x)`, an antiderivative of `c xˢ e^(bx + d)` (b < 0, x > 0). Callable through
the `IntegralWithRootSums` it belongs to.
"""
struct GammaTerm
    c::Any                      # a constant term of the user's package
    s::Q
    b::Q
    d::Q
    var::String
end
function Base.show(io::IO, g::GammaTerm)
    fr(r) = isone(denominator(r)) ? string(numerator(r)) : "$(numerator(r))/$(denominator(r))"
    one_c = string(g.c) == "1"
    print(io, "-", one_c ? "" : "($(g.c))*", iszero(g.d) ? "" : "exp($(fr(g.d)))*",
          isone(-g.b) ? "" : "($(fr(-g.b)))^($(fr(-g.s - 1)))*", "Γ(", fr(g.s + 1), ", ",
          isone(-g.b) ? "" : fr(-g.b) * "*", g.var, ")")
end
function gamma_value(g::GammaTerm, a::Number)
    c = term_value(g.c, g.var, a)
    -c * exp(Float64(g.d)) * Float64(-g.b)^(-Float64(g.s) - 1) * gamma(Float64(g.s) + 1, -Float64(g.b) * float(real(a)))
end
rs_value(g::GammaTerm, xk::String, a) = gamma_value(g, a)
rs_value_continuous(g::GammaTerm, xk::String, a::Real) = gamma_value(g, a)
depends_on(g::GammaTerm, yk::String) = g.var == yk

# the factors of a product term: (coefficient terms, exponent of x (Q), symbolic exponent terms, exp arguments),
# or nothing when a factor is not c, x^s or exp(·) (sign = -1 for a denominator)
function gamma_factors(t, xk::String, sign::Int = 1, acc = (Any[], Ref(Q(0)), Any[], Any[]))
    cs, sq, ssym, exps = acc
    if !has_x(t, xk)
        push!(cs, (t, sign))
        return acc
    end
    string(t) == xk && (sq[] += sign; return acc)
    safe_iscall(t) || return nothing
    args = arguments(t)
    n = opname(operation(t))
    if n === :*
        for a in args
            gamma_factors(a, xk, sign, acc) === nothing && return nothing
        end
        return acc
    elseif n === :/ && length(args) == 2
        gamma_factors(args[1], xk, sign, acc) === nothing && return nothing
        return gamma_factors(args[2], xk, -sign, acc)
    elseif n === :exp && length(args) == 1
        push!(exps, (args[1], sign))
        return acc
    end
    rp = radical_parts(t)
    if rp !== nothing && string(rp[2]) == xk
        sq[] += sign * rp[1]
        return acc
    end
    if n === :^ && length(args) == 2 && string(args[1]) == xk
        e = leaf_rational(args[2])
        if e !== nothing
            sq[] += sign * Q(e)
        else
            has_x(args[2], xk) && return nothing
            push!(ssym, (args[2], sign))
        end
        return acc
    end
    if n === :^ && length(args) == 2 && opname(operation(args[1])) === :exp      # exp(u)^k
        k = leaf_rational(args[2])
        k === nothing && return nothing
        push!(exps, (args[1], sign * Int(k)))          # (only integer k reach here in practice)
        return acc
    end
    nothing
end
has_x(t, xk::String) = safe_iscall(t) && !isempty(arguments(t)) ? any(a -> has_x(a, xk), arguments(t)) : string(t) == xk

# the terms of a sum
function gamma_summands(t)
    safe_iscall(t) || return Any[(t, 1)]
    args = arguments(t)
    n = opname(operation(t))
    n === :+ && return reduce(vcat, [gamma_summands(a) for a in args])
    if n === :-
        length(args) == 1 && return [(u, -s) for (u, s) in gamma_summands(args[1])]
        return vcat(gamma_summands(args[1]), reduce(vcat, [[(u, -s) for (u, s) in gamma_summands(a)] for a in args[2:end]]))
    end
    Any[(t, 1)]
end

# ∫ f dx with incomplete gamma terms, or nothing
function try_gamma(f, x; build = nothing, lift = nothing, verify::Bool = true)
    xk = string(x)
    b0 = Builder(build === nothing ? auto_build(f, x) : build, lift === nothing ? auto_lift(f, x) : lift, x)
    rest, gts, syms = Any[], Any[], Any[]
    found = false
    for (t, sg) in gamma_summands(f)
        fa = gamma_factors(t, xk)
        fa === nothing && return nothing
        cs, sq, ssym, exps = fa
        # exp(bx + d): the arguments add (exp(u)^±1)
        L = zero(QXF)
        for (u, sgn) in exps
            ue = try parse_rational(u, xk) catch; nothing end
            ue === nothing && return nothing
            L = L + kconst(Q(sgn)) * ue
        end
        s = sq[]
        if isempty(ssym) && isone(denominator(s))       # an integer power: the usual integrator
            push!(rest, sg == 1 ? t : mk(b0, :*, b0.lift(-1), t))
            continue
        end
        (isone(L.den) && degree(L.num) == 1) || return nothing
        d, b = L.num.c[1], L.num.c[2]
        b < 0 || return nothing
        cf = [(e == 1 ? u : mk(b0, :/, b0.lift(1), u)) for (u, e) in cs]
        sg == 1 || pushfirst!(cf, b0.lift(-1))
        c = isempty(cf) ? nothing : length(cf) == 1 ? cf[1] : mk(b0, :*, cf...)
        found = true
        if isempty(ssym)
            push!(gts, (c, s, b, d))
        else
            push!(syms, (c, s, ssym, b, d))
        end
    end
    found || return nothing
    terms, nums = Any[], Any[]
    arg(b) = isone(-b) ? b0.x : mk(b0, :*, cterm(b0, -b), b0.x)
    for (c, s, b, d) in gts
        g = try
            b0.build(gamma, cterm(b0, s + 1), arg(b))
        catch
            nothing
        end
        if g === nothing
            push!(nums, GammaTerm(c === nothing ? b0.lift(1) : c, s, b, d, xk))
        else
            push!(terms, gamma_product(b0, c, isone(-b) ? nothing : mk(b0, :^, cterm(b0, -b), cterm(b0, -s - 1)), d, g))
        end
    end
    for (c, s, ssym, b, d) in syms                      # s + Σ symbolic exponents: a symbolic gamma only
        sts = Any[e == 1 ? u : mk(b0, :*, b0.lift(-1), u) for (u, e) in ssym]
        iszero(s + 1) || push!(sts, cterm(b0, s + 1))
        s1 = length(sts) == 1 ? sts[1] : mk(b0, :+, sts...)       # s + 1
        g = try
            b0.build(gamma, s1, arg(b))
        catch
            return nothing
        end
        push!(terms, gamma_product(b0, c, isone(-b) ? nothing : mk(b0, :^, cterm(b0, -b), mk(b0, :*, b0.lift(-1), s1)), d, g))
    end
    if !isempty(rest)
        F = risch_integrate(length(rest) == 1 ? rest[1] : mk(b0, :+, rest...), x; build = build, lift = lift, verify = verify)
        F isa IntegralWithRootSums ? (append!(nums, F.rootsums); push!(terms, F.elementary)) : push!(terms, F)
    end
    E = isempty(terms) ? b0.lift(0) : length(terms) == 1 ? terms[1] : mk(b0, :+, terms...)
    isempty(nums) ? E : IntegralWithRootSums(E, nums, xk)
end

# -c e^d (-b)^(-s-1) Γ (factors that are 1 left out)
function gamma_product(b0::Builder, c, pw, d::Q, g)
    fs = Any[f for f in (c, pw, iszero(d) ? nothing : mk(b0, :exp, cterm(b0, d)), g) if f !== nothing]
    mk(b0, :*, b0.lift(-1), fs...)
end
