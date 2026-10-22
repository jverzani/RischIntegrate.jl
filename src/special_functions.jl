# ---------------------------------------------------------------------------
# Step 8a: non-elementary integrals with SpecialFunctions (on by default)
#
# Where the algorithm proves that ∫ a θ^j (θ = exp(U)) is not elementary, try instead
#     a = y' + jU'y + Σ_t c_t U'/(U - t) + Σ_l d_l θ_l^(-j) W_l'/W_l [+ k]
# (the parametric Risch DE in K_m, `prde`, step 9d), since (c e^(jt) Ei(j(U - t)))' = c θ^j U'/(U - t),
# (Ei(j W_l))' = θ^j θ_l^(-j) W_l'/W_l for W_l = U - a_l (θ_l = exp(a_l) a generator below), and,
# at the base for jU = A x² + B x + C₀,
# ∫ k θ^j = k e^E √π/(2√|A|) erf(√|A| (x + h))  (erfi for A > 0),  h = B/(2A), E = C₀ - B²/(4A).
# The shifts t are 0 and the constant values of U at the poles of a (U ≡ t modulo a normal
# factor of the denominator of a). At a log level whose residues are not constant,
# ∫ c' u^m u'/(log u + b) = c' e^(-kb) Ei(k (log u + b)), k = m + 1 (li(u^k) for b = 0).
# Each term keeps its exact derivative, so the usual checks still verify the result.
# ---------------------------------------------------------------------------
struct SpecialTerm
    fn::Symbol         # :Ei, :erf or :erfi
    c::Any             # coefficient ∈ C
    p::Any             # constant prefactor e^p, p ∈ C (output only: it cancels in the derivative)
    z::Any             # the argument (Ei), or x + h (erf/erfi): a tower element
    A::Q               # erf/erfi: the coefficient of x²
    deriv::Any         # the exact derivative of the term (tower element)
end

# U ∈ C(x) at r ∈ C, or nothing at a pole
function feval(U::Frac{UPoly{C}}, r::C) where {C}
    d = peval(U.den, r)
    iszero(d) ? nothing : peval(U.num, r) / d
end

# σ at level 0 (x real), for the real-form filters of special terms
conj0(T::Tower, f) = frac(cpconj_g(T.consts, f.num), cpconj_g(T.consts, f.den))

# ∫ α θ^j (θ = exp(U), level i) with Ei / erf terms: (y, terms) with ∫ α θ^j = y θ^j + Σ terms
function special_exp(T::Tower, i::Int, j::Int, α)
    lv = T.levels[i]
    m = i - 1
    C = ctype(T)
    cx = is_complex_field(C)
    U = liftto(T, lv.arg, m)
    dU = D(T, m, U)
    θj = theta(T, i)^j
    jq = cfromQ(C, Q(j))
    jU = lq(T, Q(j), m) * U
    # over ℚ(i) an Ei argument must be real or i·real (then it has a real form)
    skinds = nothing
    if cx && m > 0
        skinds = try
            sigma_kinds(T)
        catch e
            e isa RischNotImplemented ? nothing : rethrow()
        end
        skinds === nothing && return nothing
    end
    ok_arg(z) = !cx || (s = m == 0 ? conj0(T, z) : tconj(T, skinds, z, m); s == z || s == -z)
    # shifts t ∈ C: the values of U at the poles of α (U ≡ t modulo a normal factor), and 0
    shifts = C[zero(C)]
    if !isone(α.den)
        dn, _ = split_factor(T, m, α.den)
        sq = quo(dn, gcd(dn, deriv(dn)))
        if m == 0
            for r in constant_roots(sq)
                t = feval(U, r)
                (t === nothing || t in shifts) || push!(shifts, t)
            end
        elseif degree(sq) > 0                           # roots of res_θ(sq, U.num - z U.den), if constant
            R = residue_poly(T.Ts[m], sq, U.num, U.den)
            if degree(R) > 0
                cs = Any[dconst_value(T, c) for c in monic(R).c]
                if !any(isnothing, cs)
                    Rc = UPoly{C}(C[c for c in cs])
                    for t in constant_roots(quo(Rc, gcd(Rc, deriv(Rc))))
                        t in shifts || push!(shifts, t)
                    end
                end
            end
        end
    end
    extras, kinds = Any[], Any[]
    for t in shifts                                     # (e^(jt) Ei(j(U - t)))' = θ^j U'/(U - t)
        Ut = U - lconst(T, t, m)
        (iszero(Ut) || !ok_arg(lq(T, Q(j), m) * Ut)) && continue
        push!(extras, dU / Ut)
        push!(kinds, (:Ei, t))
    end
    for (l, lvl) in enumerate(T.levels[1:m])            # (Ei(j(U - a)))' = θ^j θ_l^(-j) (U - a)'/(U - a), θ_l = exp(a)
        lvl.kind === :exp || continue
        W = U - liftto(T, lvl.arg, m)
        (is_constant(T, W) || !ok_arg(lq(T, Q(j), m) * W)) && continue
        push!(extras, liftto(T, theta(T, l), m)^(-j) * D(T, m, W) / W)
        push!(kinds, (:Eigen, W))
    end
    if m == 0 && isone(jU.den) && degree(jU.num) == 2
        A = crational(jU.num.c[3])
        B, C0 = jU.num.c[2], jU.num.c[1]
        if A !== nothing && (!cx || (cconj_g(T.consts, B) == B && cconj_g(T.consts, C0) == C0))
            push!(extras, one(jU))
            push!(kinds, (:erf, A))
        end
    end
    isempty(extras) && return nothing
    # y' + j U' y + Σ c_e e = α: the parametric Risch DE in K_m (step 9d). Its solution basis
    # has (y, (c₀, c...)) with y' + jU'y = c₀ α + Σ c e; one with c₀ ≠ 0 gives the answer.
    sols = try
        prde(T, m, lq(T, Q(j), m) * dU, Any[α; extras])
    catch e
        e isa RischNotImplemented ? nothing : rethrow()
    end
    sols === nothing && return nothing
    idx = findfirst(s -> !iszero(s[2][1]), sols)
    idx === nothing && return nothing
    y0, c0 = sols[idx]
    s0 = inv(c0[1])
    y = y0 * lconst(T, s0, m)
    cs = [-(c * s0) for c in c0[2:end]]
    terms = Any[]
    X = frac(xpoly(C))
    for (c, kd, e) in zip(cs, kinds, extras)
        iszero(c) && continue
        d = lconst(T, c, i) * liftto(T, e, i) * θj         # (term)' = c e θ^j
        if kd[1] === :Ei
            t = kd[2]
            push!(terms, SpecialTerm(:Ei, c, jq * t, jU - lconst(T, jq * t, m), Q(0), d))
        elseif kd[1] === :Eigen
            push!(terms, SpecialTerm(:Ei, c, zero(C), lq(T, Q(j), m) * kd[2], Q(0), d))
        else
            A = kd[2]
            Ac = cfromQ(C, A)
            B, C0 = jU.num.c[2], jU.num.c[1]
            h = B / (Ac + Ac)
            E = C0 - B * B / (4 * Ac)
            push!(terms, SpecialTerm(A < 0 ? :erf : :erfi, c, E, X + kconst(h), A, d))
        end
    end
    y, terms
end

# a log level whose residue polynomial has non-constant roots: R/(θ + b), b ∈ C, R = c' u^m u'
function special_log(T::Tower, i::Int, R::UPoly, Dsf::UPoly)
    (degree(Dsf) == 1 && degree(R) <= 0) || return nothing
    l1 = lc(Dsf)
    if !isone(l1)                                       # make Dsf = θ + b monic
        R, Dsf = scale(inv(l1), R), scale(inv(l1), Dsf)
    end
    lv = T.levels[i]
    m0 = i - 1
    b = Dsf.c[1]
    bc = dconst_value(T, b)
    bc === nothing && return nothing
    r0 = isempty(R.c) ? zero(T.Ts[i]) : R.c[1]
    iszero(r0) && return nothing
    u = liftto(T, lv.arg, m0)
    du = D(T, m0, u)
    q = r0 / du
    mq = Q(0)
    if dconst_value(T, q) === nothing                   # q = c' u^m: m = (q'/q)/(u'/u)
        mv = dconst_value(T, D(T, m0, q) * u / (q * du))
        mv === nothing && return nothing
        mi = cinteger(mv)
        mi === nothing && return nothing
        mq = mi
    end
    mint = Int(numerator(mq))
    cv = dconst_value(T, q / u^mint)
    cv === nothing && return nothing
    k = mint + 1
    k == 0 && return nothing
    C = ctype(T)
    kc = cfromQ(C, Q(k))
    w = frac(Dsf)                                       # θ + b at level i
    d = frac(UPoly{T.Ts[i]}(T.Ts[i][r0]), Dsf)          # the integrand R/Dsf
    SpecialTerm(:Ei, cv, -(kc * bc), lconst(T, kc, i) * w, Q(0), d)
end

"""
    sinhint(x), coshint(x)

The hyperbolic sine and cosine integrals Shi(x) = (Ei(x) - Ei(-x))/2 and (Ei(x) + Ei(-x))/2 (Chi(x) for
x > 0; for x < 0 the real antiderivative of cosh(x)/x, an even function): antiderivatives of sinh(x)/x and
cosh(x)/x. SpecialFunctions.jl has neither; RischIntegrate uses them in answers (H4).
"""
sinhint(x::Real) = (expinti(x) - expinti(-x)) / 2
coshint(x::Real) = (expinti(x) + expinti(-x)) / 2
OPS[:Shi] = sinhint
OPS[:Chi] = coshint

# c₁ Ei(w) + c₂ Ei(-w) (SpecialTerms without e^p) as (c₁ + c₂) Chi(w) + (c₁ - c₂) Shi(w), when the term type
# builds sinhint and coshint calls: the terms, and the indices of the quads used (empty when none)
function shi_chi_terms(b::Builder, T::Tower, quads)
    ts, used = Any[], Set{Int}()
    for i in eachindex(quads), j in eachindex(quads)
        (i < j && !(i in used) && !(j in used)) || continue
        q1, q2 = quads[i], quads[j]
        (q1 isa SpecialTerm && q2 isa SpecialTerm && q1.fn === :Ei && q2.fn === :Ei && iszero(q1.p) && iszero(q2.p)) || continue
        levelof(T, q1.z) == levelof(T, q2.z) && q1.z == -q2.z || continue
        w = lead_rational(q1.z) < 0 ? q2.z : q1.z          # the argument with a positive leading coefficient
        c1, c2 = w == q1.z ? (q1.c, q2.c) : (q2.c, q1.c)
        wt = tower_to_term(b, T, w)
        sh, ch = try
            mk(b, :Shi, wt), mk(b, :Chi, wt)
        catch
            continue
        end
        (sh isa Number || ch isa Number) && continue
        for (c, t) in ((c1 + c2, ch), (c1 - c2, sh))
            iszero(c) || push!(ts, isone(c) ? t : mk(b, :*, cterm(b, c), t))
        end
        push!(used, i, j)
    end
    ts, used
end

# the term with a given coefficient term `ct` (real fields); zt converts a tower element
function special_out(b::Builder, q::SpecialTerm, ct, zt)
    if q.fn === :Ei
        core = mk(b, :Ei, zt(q.z))
    else
        sa = mk(b, :sqrt, cterm(b, abs(q.A)))
        core = mk(b, :*, mk(b, :/, mk(b, :sqrt, b.lift(π)), mk(b, :*, b.lift(2), sa)),
                  mk(b, q.fn, mk(b, :*, sa, zt(q.z))))
    end
    parts = Any[]
    isone(q.c) || push!(parts, ct)
    iszero(q.p) || push!(parts, mk(b, :exp, cterm(b, q.p)))
    isempty(parts) ? core : mk(b, :*, parts..., core)
end

# leading rational coefficient of a nested Frac / constant (for a sign)
lead_rational(c::Q) = c
lead_rational(c::QI) = iszero(c.re) ? c.im : c.re
lead_rational(c::QSB) = lead_rational(iszero(c.a) ? c.b : c.a)
lead_rational(c::Frac) = iszero(c) ? Q(0) : lead_rational(lc(c.num))

# Re(c e^p F(z)), F = Ei, as [(fn, w, pr, q, a, b)] meaning e^pr (a cos q + b sin q) fn(w), fn ∈ (:Ei, :Ci, :Si),
# p = pr + i ps, q = |ps| (a, b ∈ C real), so that the terms of conjugate pairs with the same function,
# argument and factor can be added before printing; nothing for erf/erfi (`special_out_real` prints them)
function special_parts_real(T::Tower, kinds, q::SpecialTerm)
    q.fn === :Ei || return nothing
    C = ctype(T)
    gens = T.consts
    half = inv(cfromQ(C, Q(2)))
    I = cimag(C)
    rpart(c) = (c + cconj_g(gens, c)) * half
    ipart(c) = (c - cconj_g(gens, c)) * inv(I + I)
    cr, ci, pr, ps = rpart(q.c), ipart(q.c), rpart(q.p), ipart(q.p)
    σ = lead_rational(ps) < 0 ? -1 : 1
    qa = σ == 1 ? ps : -ps
    # κ = e^pr (cr + i ci)(cos ps + i sin ps), sin ps = σ sin q:  κr = e^pr (cr cos q - σ ci sin q),
    # κi = e^pr (ci cos q + σ cr sin q)
    κr, κi = (cr, -σ * ci), (ci, σ * cr)
    lvl = levelof(T, q.z)
    sz = tconj(T, kinds, q.z, lvl)
    sz == q.z && return Any[(:Ei, q.z, pr, qa, κr...)]
    sz == -q.z || return nothing
    w = q.z * lconst(T, -I, lvl)
    flip = lead_rational(w) < 0
    flip && (w = -w)
    si = flip ? κi : (-κi[1], -κi[2])                   # Re(κ (Ci + i Si)) = κr Ci - κi Si
    Any[(:Ci, w, pr, qa, κr...), (:Si, w, pr, qa, si...)]
end

# Re(c e^p F(z)) over ℚ(i): Ei of a real z, or Ei(i w) ~ Ci(w) + i Si(w) for real w
function special_out_real(b::Builder, T::Tower, kinds, q::SpecialTerm)
    C = ctype(T)
    gens = T.consts
    half = inv(cfromQ(C, Q(2)))
    I = cimag(C)
    rpart(c) = (c + cconj_g(gens, c)) * half
    ipart(c) = (c - cconj_g(gens, c)) * inv(I + I)
    cr, ci, pr, ps = rpart(q.c), ipart(q.c), rpart(q.p), ipart(q.p)
    zt(z) = real_term(b, T, kinds, z)
    if q.fn !== :Ei                                      # erf/erfi: real argument and prefactor
        iszero(ci) && iszero(ps) || throw(RischNotImplemented("erf of a complex argument has no real form here"))
        iszero(cr) && return b.lift(0)
        return special_out(b, SpecialTerm(q.fn, cr, pr, q.z, q.A, q.deriv), cterm(b, cr), zt)
    end
    # κ = c e^p = e^pr (cr + i ci)(cos ps + i sin ps):  κ_r, κ_i as terms (nothing for zero)
    ep = iszero(pr) ? nothing : mk(b, :exp, cterm(b, pr))
    function combo(a1, a2)                               # e^pr (a1 cos ps + a2 sin ps)
        ts = Any[]
        if iszero(ps)
            iszero(a1) || push!(ts, cterm(b, a1))
        else
            iszero(a1) || push!(ts, mk(b, :*, cterm(b, a1), mk(b, :cos, cterm(b, ps))))
            iszero(a2) || push!(ts, mk(b, :*, cterm(b, a2), mk(b, :sin, cterm(b, ps))))
        end
        isempty(ts) && return nothing
        t = length(ts) == 1 ? ts[1] : mk(b, :+, ts...)
        ep === nothing ? t : mk(b, :*, ep, t)
    end
    κr = combo(cr, -ci)
    κi = combo(ci, cr)
    lvl = levelof(T, q.z)
    sz = tconj(T, kinds, q.z, lvl)
    if sz == q.z
        κr === nothing && return b.lift(0)
        return mk(b, :*, κr, mk(b, :Ei, zt(q.z)))
    end
    sz == -q.z || throw(RischNotImplemented("Ei of a complex argument has no real form here"))
    w = q.z * lconst(T, -I, lvl)                        # z = i w, w real
    flip = lead_rational(w) < 0                         # Ci(-w) ~ Ci(w), Si(-w) = -Si(w)
    flip && (w = -w)
    ts = Any[]
    κr === nothing || push!(ts, mk(b, :*, κr, mk(b, :Ci, zt(w))))
    if κi !== nothing                                   # Re(κ (Ci + i Si)) = κr Ci - κi Si
        st = mk(b, :*, κi, mk(b, :Si, zt(w)))
        push!(ts, flip ? st : mk(b, :*, b.lift(-1), st))
    end
    isempty(ts) && return b.lift(0)
    length(ts) == 1 ? ts[1] : mk(b, :+, ts...)
end
