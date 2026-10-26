# Step DL: dilogarithms. ∫ θ·r(x) with θ = log(a x + b) (a level over ℚ(x) only, a, b ∈ ℚ) and r ∈ ℚ(x):
# each simple pole c ∈ ℚ of r with residue ρ and K = a c + b ≠ 0 gives (s = x - c, a s + K = a x + b)
#   K > 0:  ρ (log K · log|s| - Li₂(-a s/K))          (log(K + a s) = log K + log(1 + a s/K))
#   K < 0:  ρ (½ log²(a s) + Li₂(-K/(a s)))            (log(K + a s) = log(a s) + log(1 - |K|/(a s)))
# both with derivative ρ θ/(x - c) on the domain a x + b > 0 (Li₂(z)' = -log(1 - z)/z). The term
# keeps that derivative for the exact check (as SpecialTerm); the rest of the integrand goes through
# the normal algorithm. Printed with `PolyLog.li2`, which the symbolic package must support.
# (ρ, a, b, c in the constant field: ℚ, or a parameter field ℚ(a, …) (∫ log(x)/(a + bx)); there the sign
# of K is taken at the parameter values of `param_value`, a = 1, b = 2, …, as for the step PQ forms)
# Poles in pairs: c, c̄ ∈ ℚ(i) (`DilogPairTerm`), c, c̄ ∈ ℚ(√d) real (`DilogQuadTerm`); θ = log of a product of
# linear factors: step LF (`DilogGroup`).
struct DilogTerm
    ρ::Any
    a::Any
    b::Any
    c::Any
    deriv::Any
end
# A pair of simple poles c, c̄ ∈ ℚ(i) \ ℚ (r over ℚ), residues ρ, ρ̄: with v = a x + b > 0 and K = a c + b (not real),
#   ∫ v′ log v/(v - K) = log v · log(1 - v/K) + Li₂(v/K)
# (1 - v/K and v/K stay off the cuts), and twice the real part is, α = arg K, sgn = sign(Im K),
#   ρr log v log(((v - Kr)² + Ki²)/|K|²) - 2ρi log v (atan((v - Kr)/Ki) + atan(Kr/Ki))
#     + 2ρr Re Li₂(v/|K| e^(-iα)) - 2ρi Im Li₂(v/|K| e^(-iα)),   -α = atan(Kr/Ki) - sgn π/2,
# (arg(1 - v/K) = arg(K - v) - α, continuous from 0 at v = 0); deriv: (ρ/(x - c) + ρ̄/(x - c̄)) θ.
# (over a parameter field ℚ(a, …) too: then c = cr + i ci, ρ = ρr + i ρi, a, b have parts in that field, and the sign
# of Ki is taken at `param_value`)
struct DilogPairTerm
    ρr::Any
    ρi::Any
    a::Any
    b::Any
    cr::Any              # c = cr + i ci, ci > 0
    ci::Any
    deriv::Any
end
# A pair of simple real poles c, c̄ = (-B ± √Δ)/2 ∈ ℚ(√d) \ ℚ (a factor x² + B x + C of the denominator, Δ > 0 not a
# square), residues ρ, ρ̄ ∈ ℚ(√d): the DilogTerm formulas for each, over ℚ(√d) (∫ log(x² - 1)/(x² - 2) after
# step LF; deriv: (ρ/(x - c) + ρ̄/(x - c̄)) θ).
struct DilogQuadTerm
    ρ::Any
    a::Any
    b::Any
    c::Any
    deriv::Any
end
qconj(x::QSB{D,B}) where {D,B} = QSB{D,B}(x.a, -x.b)

# Step LF: θ = log u with u = l ∏ (x - rⱼ)^eⱼ (rⱼ ∈ ℚ, more than one factor, l put into a factor with eⱼ = ±1; log(t² - 1)
# after t = √(1 + x), log((t² - 1)/(2t)) after the Euler substitution for √(x² + 1)): θ = Σ eⱼ log(x - rⱼ) where every x - rⱼ > 0, and each pole gives the terms above for each
# log(x - rⱼ), weighted by eⱼ, in one `DilogGroup` with the derivative ρ θ/(x - c) (a pole c = rⱼ: ½ log²(x - rⱼ))
struct DilogGroup
    terms::Vector{Any}
    deriv::Any
end

# the linear factors (a, b, e) of u, u = Π (a x + b)^e, or nothing
function dilog_factors(u::Frac{UPoly{C}}) where {C}
    (isone(u.den) && degree(u.num) == 1) && return [(u.num.c[2], u.num.c[1], 1)]
    C === Q || return nothing
    out = Tuple{Q,Q,Int}[]
    for (P0, sgn) in ((u.num, 1), (u.den, -1)), (g, m) in squarefree(monic(P0))
        degree(g) == 0 && continue
        for h in factor_Q(g)
            degree(h) == 1 || return nothing
            push!(out, (Q(1), h.c[1], sgn * m))
        end
    end
    length(out) >= 2 || return nothing
    # the leading coefficient l into a factor with exponent ±1: l (x - r) = l x - l r, (x - r)⁻¹/l = (l x - l r)⁻¹
    l = lc(u.num) / lc(u.den)
    if !isone(l)
        j = findfirst(((_, _, e),) -> abs(e) == 1, out)
        j === nothing && return nothing
        a, b, e = out[j]
        out[j] = (a * l, b * l, e)
    end
    out
end

function dilog_split(T::Tower, i::Int, p::UPoly)
    C = ctype(T)
    ((C === Q || real_param_field(C)) && i == 1 && T.levels[1].kind === :log && degree(p) == 1) || return nothing
    facs = dilog_factors(T.levels[1].arg)
    facs === nothing && return nothing
    single = length(facs) == 1
    r = p.c[2]                                          # coefficient of θ, ∈ ℚ(x)
    D1 = r.den
    terms = Any[]
    simple = zero(r)
    θ = frac(xpoly(T.Ts[1]))
    # the terms for one pole (pair) over the factors, as one term (one factor) or a DilogGroup
    function add!(mkterm, rs)
        ts = Any[mkterm(a, b, e) for (a, b, e) in facs]
        any(isnothing, ts) && return
        simple = simple + rs
        dv = liftto(T, rs, 1) * θ
        push!(terms, single ? ts[1](dv) : DilogGroup(Any[t(nothing) for t in ts], dv))
    end
    for c in constant_roots(D1)
        lin = UPoly{C}(C[-c, one(C)])
        iszero(rem(D1, lin * lin)) && continue           # not a simple pole
        ρ = peval(r.num, c) / peval(deriv(D1), c)
        iszero(ρ) && continue
        # K = a c + b = 0, log(a s)/s: elementary for one factor (the normal algorithm), ½ log²(a s) in a group
        add!((a, b, e) -> (single && iszero(a * c + b)) ? nothing : (dv -> DilogTerm(e * ρ, a, b, c, dv)),
             frac(UPoly{C}(C[ρ]), lin))
    end
    # pairs of poles c, c̄ = cr ± i ci: with r over ℚ the roots in ℚ(i) (the log's a, b may have parameters); over
    # ℚ(a, …) the quadratic factors of D1 with -Δ a square (atan(x - a): poles a ± i)
    two = cfromQ(C, Q(2))
    function add_pair!(cr, ci, ρr, ρi)
        num_ = UPoly{C}(C[-two * (ρr * cr + ρi * ci), two * ρr])    # ρ/(x - c) + ρ̄/(x - c̄)
        den_ = UPoly{C}(C[cr * cr + ci * ci, -two * cr, one(C)])
        add!((a, b, e) -> (dv -> DilogPairTerm(cfromQ(C, Q(e)) * ρr, cfromQ(C, Q(e)) * ρi, a, b, cr, ci, dv)),
             frac(num_, den_))
    end
    rq(c) = C === Q ? c : crational(c)
    if all(c -> rq(c) !== nothing, D1.c) && all(c -> rq(c) !== nothing, r.num.c)
        D1i = UPoly{QI}(QI[QI(rq(c), Q(0)) for c in D1.c])
        Ni = UPoly{QI}(QI[QI(rq(c), Q(0)) for c in r.num.c])
        for c in constant_roots(D1i)
            c.im > 0 || continue
            lin = UPoly{QI}(QI[-c, one(QI)])
            iszero(rem(D1i, lin * lin)) && continue
            ρ = peval(Ni, c) / peval(deriv(D1i), c)
            iszero(ρ) && continue
            add_pair!(cfromQ(C, c.re), cfromQ(C, c.im), cfromQ(C, ρ.re), cfromQ(C, ρ.im))
        end
    elseif C !== Q
        CC = cplx_type(C)
        I = cimag(CC)
        up(q) = UPoly{CC}(CC[to_complex(CC, c) for c in q.c])
        half = inv(cfromQ(CC, Q(2)))
        for (g, m) in squarefree(D1)
            (m == 1 && degree(g) == 2) || continue
            p0, p1 = g.c[1], g.c[2]
            sq = csqrt(two * two * p0 - p1 * p1)
            (sq === nothing || iszero(sq)) && continue
            cr, ci = -p1 / two, sq / two
            v = param_value(ci, T.consts)
            v === nothing && continue
            v < 0 && (ci = -ci)
            c = to_complex(CC, cr) + I * to_complex(CC, ci)
            ρ = peval(up(r.num), c) / peval(up(deriv(D1)), c)
            iszero(ρ) && continue
            ρr, ρi = to_real((ρ + cconj(ρ)) * half), to_real((ρ - cconj(ρ)) * inv(I + I))
            (ρr === nothing || ρi === nothing) && continue
            add_pair!(cr, ci, ρr, ρi)
        end
    end
    if C === Q
        # pairs of real poles in ℚ(√d)
        for (g0, m) in squarefree(monic(D1)), g in (m == 1 && degree(g0) >= 2 ? factor_Q(g0) : ())
            degree(g) == 2 || continue                  # (factor_Q needs a squarefree polynomial)
            C0, B0 = g.c[1], g.c[2]
            Δ = B0^2 - 4C0
            Δ > 0 || continue
            sq, dd = sqfree_split(numerator(Δ) * denominator(Δ))
            isone(dd) && continue
            Sd = QS{Int(dd)}
            rt = Sd(-B0 / 2, Q(sq, denominator(Δ)) / 2)      # (-B + √Δ)/2
            toS(q) = UPoly{Sd}(Sd[Sd(cc, Q(0)) for cc in q.c])
            ρ = peval(toS(r.num), rt) / peval(toS(deriv(D1)), rt)
            iszero(ρ) && continue
            ρc, cc = qconj(ρ), qconj(rt)
            num_ = UPoly{Q}(Q[-(ρ * cc + ρc * rt).a, (ρ + ρc).a])
            add!((a, b, e) -> (dv -> DilogQuadTerm(Sd(Q(e), Q(0)) * ρ, Sd(a, Q(0)), Sd(b, Q(0)), rt, dv)), frac(num_, g))
        end
    end
    isempty(terms) && return nothing
    P = typeof(p)
    (P(eltype(p.c)[p.c[1], r - simple]), terms)
end

function dilog_term(b::Builder, q::DilogTerm)
    C = typeof(q.c)
    st = poly_term(b, UPoly{C}(C[-q.c, one(C)]))       # s = x - c
    K = q.a * q.c + q.b
    li(z) = mk(b, :li2, z)          # a MethodError if the symbolic package has no method for li2
    if iszero(K)                                        # ρ ½ log²(a s) (a group of step LF)
        as = isone(q.a) ? st : mk(b, :*, cterm(b, q.a), st)
        core = mk(b, :*, cterm(b, Q(1) // 2), mk(b, :^, mk(b, :log, as), b.lift(2)))
        return isone(q.ρ) ? core : mk(b, :*, cterm(b, q.ρ), core)
    end
    Kr = crational(K)
    Kpos = Kr !== nothing ? Kr > 0 : K isa QSB ? qs_float(K) > 0 : (v = param_value(K, b.consts); v !== nothing && v > 0)
    if Kpos
        L = li(mk(b, :*, cterm(b, -q.a / K), st))
        core = isone(K) ? mk(b, :*, b.lift(-1), L) :           # log K · ½ log(s²) - Li₂(-a s/K)
               mk(b, :+, mk(b, :*, cterm(b, Q(1) // 2), mk(b, :log, cterm(b, K)), mk(b, :log, mk(b, :^, st, b.lift(2)))),
                  mk(b, :*, b.lift(-1), L))
    else
        as = isone(q.a) ? st : mk(b, :*, cterm(b, q.a), st)
        core = mk(b, :+, mk(b, :*, cterm(b, Q(1) // 2), mk(b, :^, mk(b, :log, as), b.lift(2))),
                  li(mk(b, :/, cterm(b, -K), as)))
    end
    isone(q.ρ) ? core : mk(b, :*, cterm(b, q.ρ), core)
end

qs_float(x::QS{D}) where {D} = Float64(x.a) + Float64(x.b) * sqrt(Float64(D))
dilog_group_term(b::Builder, q::DilogGroup) = mk(b, :+, Any[dilog_out(b, t) for t in q.terms]...)
dilog_out(b::Builder, q::DilogTerm) = dilog_term(b, q)
dilog_out(b::Builder, q::DilogPairTerm) = dilog_pair_term(b, q)
dilog_out(b::Builder, q::DilogQuadTerm) = dilog_quad_term(b, q)
dilog_quad_term(b::Builder, q::DilogQuadTerm) =
    mk(b, :+, dilog_term(b, DilogTerm(q.ρ, q.a, q.b, q.c, nothing)),
              dilog_term(b, DilogTerm(qconj(q.ρ), q.a, q.b, qconj(q.c), nothing)))

function dilog_pair_term(b::Builder, q::DilogPairTerm)
    C = typeof(q.a)
    Kr, Ki = q.a * q.cr + q.b, q.a * q.ci               # K = a c + b
    n2 = Kr^2 + Ki^2
    vp = UPoly{C}(C[q.b, q.a])                          # v = a x + b
    vt = poly_term(b, vp)
    lv = mk(b, :log, vt)
    ρr, ρi = q.ρr, q.ρi
    sc(c, t) = isone(c) ? t : mk(b, :*, cterm(b, c), t)
    ts = Any[]
    if !iszero(ρr)                                      # ρr log v log(((v - Kr)² + Ki²)/|K|²)
        w = UPoly{C}(C[q.b - Kr, q.a])
        w2 = w * w + UPoly{C}(C[Ki^2])
        push!(ts, sc(ρr, mk(b, :*, lv, mk(b, :log, poly_term(b, UPoly{C}(C[c / n2 for c in w2.c]))))))
    end
    if !iszero(ρi)                                      # -2ρi log v (atan((v - Kr)/Ki) + atan(Kr/Ki))
        at = mk(b, :atan, poly_term(b, UPoly{C}(C[(q.b - Kr) / Ki, q.a / Ki])))
        iszero(Kr) || (at = mk(b, :+, at, mk(b, :atan, cterm(b, Kr / Ki))))
        push!(ts, sc(cfromQ(C, Q(-2)) * ρi, mk(b, :*, lv, at)))
    end
    m = csqrt(n2)                                       # v/|K|
    m === nothing || C === Q || (v = param_value(m, b.consts); (v !== nothing && v < 0) && (m = -m))
    ρt = m === nothing ? mk(b, :/, vt, mk(b, :sqrt, cterm(b, n2))) : poly_term(b, UPoly{C}(C[c / m for c in vp.c]))
    Kir = C === Q ? Ki : crational(Ki)
    Kipos = Kir !== nothing ? Kir > 0 : (v = param_value(Ki, b.consts); v !== nothing && v > 0)
    hp = mk(b, :*, cterm(b, Q(Kipos ? -1 : 1, 2)), b.lift(π))
    φt = iszero(Kr) ? hp : mk(b, :+, mk(b, :atan, cterm(b, Kr / Ki)), hp)
    iszero(ρr) || push!(ts, sc(cfromQ(C, Q(2)) * ρr, mk(b, :ReLi, b.lift(2), ρt, φt)))
    iszero(ρi) || push!(ts, sc(cfromQ(C, Q(-2)) * ρi, mk(b, :ImLi, b.lift(2), ρt, φt)))
    length(ts) == 1 ? ts[1] : mk(b, :+, ts...)
end
