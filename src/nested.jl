# ---------------------------------------------------------------------------
# Nested square roots that do not denest: y₂ = √(a + b y₁), y₁ = √c (a, b, c ∈ ℚ(x)), with
# e = a² - b²c = -s² (s ∈ ℚ(x)), e.g. √(√(1 + x⁴) - x²) (e = -1).
#
# y₂ y₂′ = √e = i s for the conjugate y₂′ = √(a - b y₁), so over ℚ(i)(x) the field ℚ(i)(x, y₁, y₂) is
# biquadratic: u₁ = y₂ + i s/y₂ and u₃ = y₂ - i s/y₂ = ū₁ with u₁² = 2a + 2is, u₃² = 2a - 2is,
# y₁ = u₁u₃/(2b). In the basis 1, y₁, y₂, y₁y₂ an integrand is f₀ + f₁y₁ + f₂y₂ + f₃y₁y₂, and
#   f₂y₂ + f₃y₁y₂ = g u₁ + ḡ ū₁,   g = (f₂ + a f₃/b)/2 - i s f₃/(2b),
# so ∫ f = ∫ f₀ + ∫ f₁ √c + 2 Re ∫ g u₁ (each part by Liouville, as in step BQ). For u₁² of degree ≤ 2
# (genus 0) ∫ g u₁ is an Euler substitution over ℚ(i): a rational integral over ℚ(i) in t (verified
# exactly), with t written back as an element τ of ℚ(i)(x)⟨1, y₁, y₂, y₁y₂⟩. Real parts are exact:
# Re(c log W) = cᵣ ½ log(W_re² + W_im²) - cᵢ atan(W_im/W_re), W_re, W_im in the real field ℚ(x)⟨…⟩.
# ---------------------------------------------------------------------------

# c₀ + c₁y₁ + c₂y₂ + c₃y₁y₂, y₁² = C, y₂² = A + B y₁ (A, B, C in the coefficient field)
struct NestEl{F}
    c::NTuple{4,F}
end
nest_add(u::NestEl, v::NestEl) = NestEl(u.c .+ v.c)
nest_neg(u::NestEl) = NestEl(map(-, u.c))
nest_scale(k, u::NestEl) = NestEl(map(t -> k * t, u.c))
function nest_mul(abc, u::NestEl, v::NestEl)
    A, B, C = abc
    (p0, p1, p2, p3), (q0, q1, q2, q3) = u.c, v.c
    m23 = p2 * q3 + p3 * q2
    NestEl((p0 * q0 + C * p1 * q1 + A * p2 * q2 + B * C * m23 + A * C * p3 * q3,
            p0 * q1 + p1 * q0 + B * p2 * q2 + A * m23 + B * C * p3 * q3,
            p0 * q2 + p2 * q0 + C * (p1 * q3 + p3 * q1),
            p0 * q3 + p3 * q0 + p1 * q2 + p2 * q1))
end
function nest_inv(abc, u::NestEl{F}) where {F}
    basis = [NestEl(ntuple(i -> i == j ? one(F) : zero(F), 4)) for j in 1:4]
    cols = [collect(nest_mul(abc, u, e).c) for e in basis]
    sol = solve_columns(cols, F[one(F), zero(F), zero(F), zero(F)])
    sol === nothing && throw(DivideError())
    NestEl(Tuple(sol))
end
function nest_pow(abc, u::NestEl{F}, k::Integer) where {F}
    k < 0 && return nest_pow(abc, nest_inv(abc, u), -k)
    r, b = NestEl((one(F), zero(F), zero(F), zero(F))), u
    while k > 0
        isodd(k) && (r = nest_mul(abc, r, b))
        k >>= 1
        k > 0 && (b = nest_mul(abc, b, b))
    end
    r
end
nest_const(f::F) where {F} = NestEl((f, zero(f), zero(f), zero(f)))

# the term t as a NestEl over ℚ(x); `outer` recognises the radicand of y₂
function parse_nest(t, xk::String, abc, c::QXF, outer)
    if safe_iscall(t)
        args = arguments(t)
        if !isempty(args)
            rp = radical_parts(t)
            if rp !== nothing
                e, ut = rp
                k = 2 * e
                isone(denominator(k)) || throw(RischNotImplemented("radical $t of index > 2 in a nested radical"))
                k = Int(numerator(k))
                ue = radicand_element(ut, xk)
                ue == c && return nest_pow(abc, NestEl((zero(QXF), one(QXF), zero(QXF), zero(QXF))), k)
                ue === nothing && outer(ut) &&
                    return nest_pow(abc, NestEl((zero(QXF), zero(QXF), one(QXF), zero(QXF))), k)
                throw(RischNotImplemented("radical $t: not √c or the nested radical"))
            end
            n = opname(operation(t))
            v = [parse_nest(u, xk, abc, c, outer) for u in args]
            n === :+ && return foldl(nest_add, v)
            n === :- && return length(v) == 1 ? nest_neg(v[1]) : nest_add(v[1], nest_neg(foldl(nest_add, v[2:end])))
            n === :* && return foldl((f, g) -> nest_mul(abc, f, g), v)
            n === :/ && length(v) == 2 && return nest_mul(abc, v[1], nest_inv(abc, v[2]))
            n === :inv && length(v) == 1 && return nest_inv(abc, v[1])
            if n === :^ && length(v) == 2
                k = all(iszero, v[2].c[2:4]) ? const_int(v[2].c[1]) : nothing
                (k === nothing || abs(k) > 10_000) && throw(RischNotImplemented("only small integer powers are supported"))
                return nest_pow(abc, v[1], k)
            end
            throw(RischNotImplemented("`$n` in a nested-radical integrand"))
        end
    end
    string(t) == xk && return nest_const(frac(xpoly(Q)))
    r = leaf_rational(t)
    r !== nothing && return nest_const(kconst(r))
    throw(RischNotImplemented("symbol `$t` is not the integration variable"))
end

# ℚ(x) → ℚ(i)(x) and real/imaginary parts of f ∈ ℚ(i)(x) at real x
const QIX = UPoly{QI}
toqi(f::QXF) = frac(toQI(f.num), toQI(f.den))
qi_conj(p::QIX) = QIX(QI[QI(c.re, -c.im) for c in p.c])
function qi_reim(f::Frac{QIX})
    n, d = f.num * qi_conj(f.den), f.den * qi_conj(f.den)        # d is real
    re(p) = QX(Q[c.re for c in p.c])
    im(p) = QX(Q[c.im for c in p.c])
    dd = re(d)
    frac(re(n), dd), frac(im(n), dd)
end
nest_reim(u::NestEl) = (rs = map(qi_reim, u.c); (NestEl(map(first, rs)), NestEl(map(last, rs))))
# a polynomial over ℚ(i) evaluated at a NestEl
nest_eval(abc, p::QIX, τ::NestEl{F}) where {F} =
    foldr((c, acc) -> nest_add(nest_mul(abc, acc, τ), nest_const(frac(QIX([c])))), p.c; init = nest_const(zero(F)))

# a NestEl over ℚ(x) as a term
function nest_term(b0::Builder, u::NestEl, y1t, y2t)
    ts = Any[]
    for (k, c) in enumerate(u.c)
        iszero(c) && continue
        basis = k == 1 ? nothing : k == 2 ? y1t : k == 3 ? y2t : mk(b0, :*, y1t, y2t)
        ct = frac_term(b0, c)
        push!(ts, basis === nothing ? ct : isone(c) ? basis : mk(b0, :*, ct, basis))
    end
    isempty(ts) ? b0.lift(0) : length(ts) == 1 ? ts[1] : mk(b0, :+, ts...)
end

# ∫ f dx for f with nested radicals √(a + b√c), a² - b²c = -s²; nothing when not of this shape
function integrate_nested(f, x, xk::String, b0::Builder; verify::Bool = true)
    rads = collect_radicals(f, xk)
    nested = [(e, u) for (e, u) in rads if radicand_element(u, xk) === nothing]
    isempty(nested) && return nothing
    ut0 = nested[1][2]
    inner = collect_radicals(ut0, xk)
    cs = [radicand_element(u, xk) for (_, u) in inner]
    (isempty(cs) || any(isnothing, cs) || any(c -> c != cs[1], cs)) && return nothing
    c = cs[1]
    ab = try
        parse_hyp(ut0, xk, c, (ue, ei) -> (ue == c && isinteger(2 * ei)) ? Int(2 * ei) : nothing)
    catch err
        err isa RischNotImplemented || rethrow()
        return nothing
    end
    a, b = ab.p, ab.q
    iszero(b) && return nothing
    s = csqrt(b * b * c - a * a)                        # e = a² - b²c = -s²
    s === nothing && return nothing
    outer = ut -> (r = try parse_hyp(ut, xk, c, (ue, ei) -> (ue == c && isinteger(2 * ei)) ? Int(2 * ei) : nothing) catch; nothing end;
                   r !== nothing && r.p == a && r.q == b)
    abc = (a, b, c)
    el = parse_nest(f, xk, abc, c, outer)
    f0, f1, f2, f3 = el.c
    e = a * a - b * b * c
    I = kconst(QI(Q(0), Q(1)))
    half = kconst(QI(Q(1, 2), Q(0)))
    qa, qb, qs, qe = toqi(a), toqi(b), toqi(s), toqi(e)
    g = (toqi(f2) + qa * toqi(f3) / qb) * half - I * qs * toqi(f3) / (qb + qb)
    terms = Any[]
    kw = (build = b0.build, lift = b0.lift, verify = verify)
    iszero(f0) || push!(terms, risch_integrate(frac_term(b0, f0), x; kw...))
    y1t = mk(b0, :sqrt, frac_term(b0, c))
    iszero(f1) || push!(terms, risch_integrate(mk(b0, :*, frac_term(b0, f1), y1t), x; kw...))
    if !iszero(g)
        # u₁² = A₁ = 2a + 2is: an Euler substitution over ℚ(i) when A₁ is a polynomial of degree ≤ 2
        A1 = toqi(a) + toqi(a) + I * (qs + qs)
        (isone(A1.den) && degree(A1.num) <= 2) || throw(RischNotImplemented(
            "a nested radical whose conjugate pieces √(2a ± 2is) are not square roots of quadratics"))
        co(i) = i <= length(A1.num.c) ? A1.num.c[i] : zero(QI)
        γ, β, α = co(1), co(2), co(3)
        P = QIX
        t = frac(xpoly(QI))
        kq(z) = frac(P([z]))
        # u₁ = y₂ + i s/y₂ = y₂ + i s y₂ (a - b y₁)/e as an element of ℚ(i)(x)⟨…⟩
        u1 = NestEl((zero(Frac{P}), zero(Frac{P}), kq(one(QI)) + I * qs * qa / qe, -(I * qs * qb / qe)))
        xn = nest_const(frac(xpoly(QI)))
        abcI = (qa, qb, toqi(c))
        if iszero(α)                                    # u₁² = βx + γ: x = (t² - γ)/β, u₁ = t
            iszero(β) && throw(RischNotImplemented("a constant conjugate radicand"))
            φ, ψ = (t * t - kq(γ)) / kq(β), t
            τ = u1
        elseif (sγ = qi_sqrt(γ)) !== nothing && !iszero(γ)   # u₁ = x t + √γ
            φ = (kq(sγ + sγ) * t - kq(β)) / (kq(α) - t * t)
            ψ = φ * t + kq(sγ)
            τ = nest_mul(abcI, nest_add(u1, nest_const(kq(-sγ))), nest_inv(abcI, xn))
        elseif (sα = qi_sqrt(α)) !== nothing            # u₁ = t - √α x
            φ = (t * t - kq(γ)) / (kq(β) + kq(sα + sα) * t)
            ψ = t - kq(sα) * φ
            τ = nest_add(u1, nest_mul(abcI, nest_const(kq(sα)), xn))
        else
            throw(RischNotImplemented("an Euler substitution over ℚ(i) for √($(A1.num)) (no square root of α, γ)"))
        end
        gφ = foldr((cc, acc) -> acc * φ + kq(cc), g.num.c; init = zero(t)) /
             foldr((cc, acc) -> acc * φ + kq(cc), g.den.c; init = zero(t))
        G = gφ * ψ * dx(φ)
        res = integrate_rational(G)
        (isempty(res.atans) && isempty(res.unresolved) && isempty(res.quads)) || throw(RischNotImplemented(
            "the conjugate piece of a nested radical needs residues outside ℚ(i)"))
        derivative_of(res) == G || throw(RischError("internal check failed: the rational integral over ℚ(i)"))
        # 2 Re[R(τ) + Σ c log w(τ)] = 2 Re R(τ) + Σ (cᵣ log|w|² - 2cᵢ atan(Im w/Re w))
        y2t = mk(b0, :sqrt, ut0)
        R = res.rational
        Rτ = nest_mul(abcI, nest_eval(abcI, R.num, τ), nest_inv(abcI, nest_eval(abcI, R.den, τ)))
        Rre, _ = nest_reim(Rτ)
        all(iszero, Rre.c) || push!(terms, nest_term(b0, nest_scale(kconst(Q(2)), Rre), y1t, y2t))
        for (cc, w) in res.logs
            W = nest_eval(abcI, w, τ)
            Wr, Wi = nest_reim(W)
            if !iszero(cc.re)
                m2 = nest_add(nest_mul(abc, Wr, Wr), nest_mul(abc, Wi, Wi))
                push!(terms, mk(b0, :*, cterm(b0, cc.re), mk(b0, :log, nest_term(b0, m2, y1t, y2t))))
            end
            if !iszero(cc.im)
                push!(terms, mk(b0, :*, cterm(b0, -2 * cc.im),
                                mk(b0, :atan, mk(b0, :/, nest_term(b0, Wi, y1t, y2t), nest_term(b0, Wr, y1t, y2t)))))
            end
        end
    end
    isempty(terms) ? b0.lift(0) : length(terms) == 1 ? terms[1] : mk(b0, :+, terms...)
end
