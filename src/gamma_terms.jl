# ---------------------------------------------------------------------------
# Phase 6, H3: incomplete gamma answers. For b < 0 and s ∉ ℤ (rational, or a symbolic exponent):
#   ∫ xˢ e^(bx + d) dx = -e^d (-b)^(-s-1) Γ(s + 1, -bx)      (x > 0; d/dw Γ(s+1, w) = -wˢ e^(-w))
# Tried when the Risch machinery decides NotElementary for a sum of terms C xˢ exp(bx + d); terms with an
# integer s are integrated as usual. The Γ term is a symbolic `gamma(s + 1, -bx)` call when the term type
# can build one (Expr, …), else a `GammaTerm` evaluated numerically (numeric s only), as for ₂F₁.
# ---------------------------------------------------------------------------
using SpecialFunctions: gamma
using HypergeometricFunctions: _₁F₁, pFq
OPS[:_₁F₁] = _₁F₁                                       # (evaluating answers with a ₁F₁ term)

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
    elseif n === :^ && length(args) == 2 && is_e_const(args[1])   # e^u (SymEngine's form of exp(u))
        push!(exps, (args[2], sign))
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
    if n === :^ && length(args) == 2 && safe_iscall(args[1]) && opname(operation(args[1])) === :exp   # exp(u)^k
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
    @nospecialize f x
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
        iszero(b) && return nothing                     # (b > 0: ₁F₁, below)
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
        if b > 0                                        # e^d x^(s+1)/(s+1) ₁F₁(s+1; s+2; bx)
            r = terms_or_nums(b0, c, cterm(b0, s + 1), b, d, KummerTerm(c === nothing ? b0.lift(1) : c, s, b, d, xk))
            push!(r[1] === terms_marker ? terms : nums, r[2])
            continue
        end
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
        if b > 0                                        # a symbolic ₁F₁ only
            kt = terms_or_nums(b0, c, s1, b, d, nothing)
            kt === nothing && return nothing
            push!(terms, kt[2])
            continue
        end
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

# b > 0: (terms or nums, c e^d x^(s+1)/(s+1) ₁F₁(s+1; s+2; bx)) with s1 = s + 1 a term; the symbolic
# ₁F₁ when the term type builds one, else the numeric term `num` (nothing: no answer)
function terms_or_nums(b0::Builder, c, s1, b::Q, d::Q, num)
    xs = b0.x
    g = try
        b0.build(_₁F₁, s1, mk(b0, :+, s1, b0.lift(1)), isone(b) ? xs : mk(b0, :*, cterm(b0, b), xs))
    catch
        nothing
    end
    if g === nothing || g isa Number
        num === nothing && return nothing
        return (nums_marker, num)
    end
    fs = Any[f for f in (c, iszero(d) ? nothing : mk(b0, :exp, cterm(b0, d)),
                         mk(b0, :/, mk(b0, :^, xs, s1), s1), g) if f !== nothing]
    (terms_marker, mk(b0, :*, fs...))
end
const terms_marker, nums_marker = :terms, :nums

"""
    KummerTerm

`c e^d x^(s+1)/(s+1) ₁F₁(s+1; s+2; b x)`, an antiderivative of `c xˢ e^(bx + d)` (b > 0, x > 0), evaluated
numerically through the `IntegralWithRootSums` it belongs to (term types without a ₁F₁ term).
"""
struct KummerTerm
    c::Any
    s::Q
    b::Q
    d::Q
    var::String
end
function Base.show(io::IO, g::KummerTerm)
    fr(r) = isone(denominator(r)) ? string(numerator(r)) : "$(numerator(r))/$(denominator(r))"
    print(io, string(g.c) == "1" ? "" : "($(g.c))*", iszero(g.d) ? "" : "exp($(fr(g.d)))*",
          g.var, "^(", fr(g.s + 1), ")/(", fr(g.s + 1), ")*₁F₁(", fr(g.s + 1), ", ", fr(g.s + 2), "; ",
          isone(g.b) ? "" : fr(g.b) * "*", g.var, ")")
end
function kummer_value(g::KummerTerm, a::Number)
    c = term_value(g.c, g.var, a)
    s1 = Float64(g.s + 1)
    x = float(real(a))
    c * exp(Float64(g.d)) * x^s1 / s1 * _₁F₁(s1, s1 + 1, Float64(g.b) * x)
end
rs_value(g::KummerTerm, xk::String, a) = kummer_value(g, a)
rs_value_continuous(g::KummerTerm, xk::String, a::Real) = kummer_value(g, a)
depends_on(g::KummerTerm, yk::String) = g.var == yk

# -c e^d (-b)^(-s-1) Γ (factors that are 1 left out)
function gamma_product(b0::Builder, c, pw, d::Q, g)
    fs = Any[f for f in (c, pw, iszero(d) ? nothing : mk(b0, :exp, cterm(b0, d)), g) if f !== nothing]
    mk(b0, :*, b0.lift(-1), fs...)
end

# H3 through x = eᵘ: f(x) with log x (∫ 1/log(x)^(n+1) = ∫ e^u u^(-n-1) du), g(u) = f(eᵘ)·eᵘ with log x ↦ u
# (u printed as x), integrated by `try_gamma`, and u = log x put back. Nothing when f has no log x or g is
# not of the gamma kind.
function try_gamma_log(f, x; build = nothing, lift = nothing, verify::Bool = true)
    @nospecialize f x
    xk = string(x)
    islogx(t) = isnode(t) && opname(operation(t)) === :log && length(arguments(t)) == 1 && string(arguments(t)[1]) == xk
    haslog(t) = islogx(t) || (isnode(t) && any(haslog, arguments(t)))
    haslog(f) || return nothing
    b0 = Builder(build === nothing ? auto_build(f, x) : build, lift === nothing ? auto_lift(f, x) : lift, x)
    ex = mk(b0, :exp, b0.x)
    sub(t) = islogx(t) ? b0.x : isnode(t) ? term_rebuild(b0, t, Any[sub(a) for a in arguments(t)]) : (string(t) == xk ? ex : t)
    G = try_gamma(mk(b0, :*, sub(f), ex), x; build = build, lift = lift, verify = verify)
    G === nothing && return nothing
    lx = mk(b0, :log, b0.x)
    back(t) = isnode(t) ? term_rebuild(b0, t, Any[back(a) for a in arguments(t)]) : (string(t) == xk ? lx : t)
    G isa IntegralWithRootSums && return nothing        # (numeric terms are in u)
    back(G)
end

# H4: ∫ c xˢ cos(bx), ∫ c xˢ sin(bx) for s ∉ ℤ rational (x > 0), by the series termwise:
#   ∫ xˢ cos(bx) = x^(s+1)/(s+1) ₁F₂((s+1)/2; 1/2, (s+3)/2; -b²x²/4)
#   ∫ xˢ sin(bx) = b x^(s+2)/(s+2) ₁F₂((s+2)/2; 3/2, (s+4)/2; -b²x²/4)
# Real forms (no complex Γ). The terms are `TrigPowerTerm`s, evaluated numerically.
struct TrigPowerTerm
    c::Any
    s::Q
    b::Q
    issin::Bool
    var::String
end
function Base.show(io::IO, g::TrigPowerTerm)
    fr(r) = isone(denominator(r)) ? string(numerator(r)) : "$(numerator(r))/$(denominator(r))"
    e = g.s + (g.issin ? 2 : 1)
    a = e / 2
    print(io, string(g.c) == "1" ? "" : "($(g.c))*", (g.issin && !isone(g.b)) ? "($(fr(g.b)))*" : "", g.var, "^(", fr(e), ")/(", fr(e),
          ")*₁F₂(", fr(a), "; ", g.issin ? "3/2" : "1/2", ", ", fr(a + 1), "; -", fr(g.b^2 / 4), "*", g.var, "^2)")
end
function trigpower_value(g::TrigPowerTerm, a::Number)
    c = term_value(g.c, g.var, a)
    x = float(real(a))
    e = Float64(g.s) + (g.issin ? 2 : 1)
    b = Float64(g.b)
    z = -b^2 * x^2 / 4
    v = x^e / e * pFq((e / 2,), (g.issin ? 1.5 : 0.5, e / 2 + 1), z)
    c * (g.issin ? b * v : v)
end
rs_value(g::TrigPowerTerm, xk::String, a) = trigpower_value(g, a)
rs_value_continuous(g::TrigPowerTerm, xk::String, a::Real) = trigpower_value(g, a)
depends_on(g::TrigPowerTerm, yk::String) = g.var == yk

function try_trig_power(f, x; build = nothing, lift = nothing, verify::Bool = true)
    @nospecialize f x
    xk = string(x)
    b0 = Builder(build === nothing ? auto_build(f, x) : build, lift === nothing ? auto_lift(f, x) : lift, x)
    nums, rest = Any[], Any[]
    syms = Any[]                                        # symbolic exponents: an Expr pFq term
    for (t, sg) in gamma_summands(f)
        cs, sq, trig, ssym = Any[], Ref(Q(0)), Any[], Any[]
        ok = trig_factors!(t, xk, 1, cs, sq, trig, ssym)
        if !ok || length(trig) != 1 || (isempty(ssym) && isone(denominator(sq[])))
            push!(rest, sg == 1 ? t : mk(b0, :*, b0.lift(-1), t))
            continue
        end
        issin, bq = trig[1]
        cf = Any[e == 1 ? u : mk(b0, :/, b0.lift(1), u) for (u, e) in cs]
        sg == 1 || pushfirst!(cf, b0.lift(-1))
        c = isempty(cf) ? b0.lift(1) : length(cf) == 1 ? cf[1] : mk(b0, :*, cf...)
        # sin(-bx) = -sin(bx), cos(-bx) = cos(bx)
        if bq < 0
            bq = -bq
            issin && (c = mk(b0, :*, b0.lift(-1), c))
        end
        if isempty(ssym)
            push!(nums, TrigPowerTerm(c, sq[], bq, issin, xk))
        else
            b0.x isa Symbol || return nothing           # (other term types: through Expr, `special_fallback`)
            sts = Any[e == 1 ? u : mk(b0, :*, b0.lift(-1), u) for (u, e) in ssym]
            push!(sts, cterm(b0, sq[] + (issin ? 2 : 1)))
            et = mk(b0, :+, sts...)                     # s + 1 (cos) or s + 2 (sin)
            half = mk(b0, :/, et, b0.lift(2))
            z = mk(b0, :*, cterm(b0, -bq^2 / 4), mk(b0, :^, b0.x, b0.lift(2)))
            pf = Expr(:call, :pFq, Expr(:tuple, half), Expr(:tuple, issin ? 3 // 2 : 1 // 2, mk(b0, :+, half, b0.lift(1))), z)
            fs = Any[mk(b0, :/, mk(b0, :^, b0.x, et), et), pf]
            string(c) == "1" || pushfirst!(fs, c)
            issin && !isone(bq) && insert!(fs, 1, cterm(b0, bq))
            push!(syms, mk(b0, :*, fs...))
        end
    end
    (isempty(nums) && isempty(syms)) && return nothing
    E = isempty(syms) ? b0.lift(0) : length(syms) == 1 ? syms[1] : mk(b0, :+, syms...)
    if !isempty(rest)
        F = risch_integrate(length(rest) == 1 ? rest[1] : mk(b0, :+, rest...), x; build = build, lift = lift, verify = verify)
        F isa IntegralWithRootSums ? (append!(nums, F.rootsums); E = mk(b0, :+, E, F.elementary)) : (E = mk(b0, :+, E, F))
    end
    isempty(nums) ? E : IntegralWithRootSums(E, nums, xk)
end
# factors of a product: constants (cs), x^s (sq), sin/cos(b x) with b ∈ ℚ (trig); false if another factor
function trig_factors!(t, xk, sign, cs, sq, trig, ssym)
    has_x(t, xk) || (push!(cs, (t, sign)); return true)
    string(t) == xk && (sq[] += sign; return true)
    safe_iscall(t) || return false
    args = arguments(t)
    n = opname(operation(t))
    n === :* && return all(a -> trig_factors!(a, xk, sign, cs, sq, trig, ssym), args)
    if n === :/ && length(args) == 2
        return trig_factors!(args[1], xk, sign, cs, sq, trig, ssym) && trig_factors!(args[2], xk, -sign, cs, sq, trig, ssym)
    end
    rp = radical_parts(t)
    (rp !== nothing && string(rp[2]) == xk) && (sq[] += sign * rp[1]; return true)
    if n === :^ && length(args) == 2 && string(args[1]) == xk
        e = leaf_rational(args[2])
        if e === nothing
            has_x(args[2], xk) && return false
            push!(ssym, (args[2], sign))                # a symbolic exponent
        else
            sq[] += sign * Q(e)
        end
        return true
    end
    if n in (:sin, :cos) && length(args) == 1 && sign == 1
        u = try parse_rational(args[1], xk) catch; nothing end
        (u !== nothing && isone(u.den) && degree(u.num) == 1 && iszero(u.num.c[1])) || return false
        push!(trig, (n === :sin, u.num.c[2]))
        return true
    end
    false
end

# Q eᵛ with the exponentials of each summand of Q merged into eᵛ: (x - 1)eˣ e^(-x²) as x e^(x - x²) - e^(x - x²),
# whose erf terms step SF finds (eˣ e^(-x²) is two exponentials there)
function times_exp(b0::Builder, Q, ex)
    v = arguments(ex)[1]
    ss = (safe_iscall(Q) && opname(operation(Q)) === :+) ? arguments(Q) : Any[Q]
    ts = Any[]
    for s in ss
        args, rest = Any[v], Any[]
        for (t, e) in product_factors!(Any[], s, 1)
            if safe_iscall(t) && opname(operation(t)) === :exp && length(arguments(t)) == 1
                push!(args, e == 1 ? arguments(t)[1] : mk(b0, :*, b0.lift(e), arguments(t)[1]))
            else
                push!(rest, e == 1 ? t : mk(b0, :^, t, b0.lift(e)))
            end
        end
        E = mk(b0, :exp, length(args) == 1 ? v : mk(b0, :+, args...))
        push!(ts, isempty(rest) ? E : mk(b0, :*, rest..., E))
    end
    length(ts) == 1 ? ts[1] : mk(b0, :+, ts...)
end

# ∫ c·erf(ax + b) = c (x + b/a) erf(ax + b) + c e^(-(ax+b)²)/(a√π); erfi: c (x + b/a) erfi(ax + b) - c e^((ax+b)²)/(a√π)
# (by parts). With a factor A(x) free of erf (SymPy #29909, eˣ erf x), by parts with Q = ∫ A:
#   ∫ A erf(u) = Q erf(u) - (2a/√π) ∫ Q e^(-u²),   erfi: Q erfi(u) - (2a/√π) ∫ Q e^(u²)
# when Q is elementary (no RootSum) and the second integral is found (erf terms: step SF). A sum of such terms and
# terms free of erf; nothing when f has another use of erf, or a part is refused.
function try_erf(f, x; build = nothing, lift = nothing, verify::Bool = true)
    @nospecialize f x
    xk = string(x)
    haserf(t) = isnode(t) && (opname(operation(t)) in (:erf, :erfi) || any(haserf, arguments(t)))
    haserf(f) || return nothing
    b0 = Builder(build === nothing ? auto_build(f, x) : build, lift === nothing ? auto_lift(f, x) : lift, x)
    terms, rest = Any[], Any[]
    for (t, sg) in gamma_summands(f)
        if !haserf(t)
            push!(rest, sg == 1 ? t : mk(b0, :*, b0.lift(-1), t))
            continue
        end
        facs = Any[]
        flat(u) = (isnode(u) && opname(operation(u)) === :*) ? foreach(flat, arguments(u)) : push!(facs, u)
        flat(t)
        es = [u for u in facs if haserf(u)]
        length(es) == 1 || return nothing
        e = es[1]
        (opname(operation(e)) in (:erf, :erfi) && length(arguments(e)) == 1) || return nothing
        cs = [u for u in facs if u !== e]
        xs = [u for u in cs if depends_on(u, xk)]       # A(x)
        any(haserf, xs) && return nothing
        cs = [u for u in cs if !depends_on(u, xk)]
        u = arguments(e)[1]
        T, ue = try                                     # a x + b, a and b constants (parameters allowed)
            build_tower(u, xk)
        catch err
            (err isa RischNotImplemented || err isa RischError) || rethrow()
            return nothing
        end
        (isempty(T.levels) && isone(ue.den) && degree(ue.num) == 1) || return nothing
        a, b = ue.num.c[2], ue.num.c[1]
        bc = Builder(b0.build, b0.lift, b0.x, T.consts)
        isf = opname(operation(e)) === :erf
        c = isempty(cs) ? (sg == 1 ? nothing : b0.lift(-1)) : mk(b0, :*, b0.lift(sg), cs...)
        ex = mk(b0, :exp, isf ? mk(b0, :*, b0.lift(-1), mk(b0, :^, u, b0.lift(2))) : mk(b0, :^, u, b0.lift(2)))
        if !isempty(xs)
            A = length(xs) == 1 ? xs[1] : mk(b0, :*, xs...)
            tt = try
                Qt = risch_integrate(A, x; build = build, lift = lift, verify = verify)
                Qt isa IntegralWithRootSums && return nothing
                H = risch_integrate(times_exp(b0, Qt, ex), x; build = build, lift = lift, verify = verify)
                H isa IntegralWithRootSums && return nothing
                k = mk(b0, :/, isone(a) ? b0.lift(2) : mk(b0, :*, b0.lift(2), cterm(bc, a)), mk(b0, :sqrt, b0.lift(π)))
                mk(b0, :+, mk(b0, :*, Qt, e), mk(b0, :*, b0.lift(-1), k, H))
            catch err
                (err isa RischNotImplemented || err isa NotElementary) || rethrow()
                return nothing
            end
            push!(terms, c === nothing ? tt : mk(b0, :*, c, tt))
            continue
        end
        xb = iszero(b) ? b0.x : mk(b0, :+, b0.x, cterm(bc, b / a))
        q = mk(b0, :/, ex, isone(a) ? mk(b0, :sqrt, b0.lift(π)) : mk(b0, :*, cterm(bc, a), mk(b0, :sqrt, b0.lift(π))))
        tt = mk(b0, :+, mk(b0, :*, xb, e), isf ? q : mk(b0, :*, b0.lift(-1), q))
        push!(terms, c === nothing ? tt : mk(b0, :*, c, tt))
    end
    isempty(terms) && return nothing
    if !isempty(rest)
        F = risch_integrate(length(rest) == 1 ? rest[1] : mk(b0, :+, rest...), x; build = build, lift = lift, verify = verify)
        F isa IntegralWithRootSums && return nothing
        push!(terms, F)
    end
    length(terms) == 1 ? terms[1] : mk(b0, :+, terms...)
end
