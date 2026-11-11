# ---------------------------------------------------------------------------
# Step MR (SI2 phase 5, first part): radicals of functions of one exponential or trigonometric
# monomial, removed by a substitution. f has radicals rⱼ = Uⱼ^eⱼ with Uⱼ rational in θ (θ = e^(kx), or
# θ = e^(ikx) over ℚ(i) for sin, cos, tan of kx). f is parsed with each rⱼ an opaque constant (step SY):
# f = R(θ). If R and every Uⱼ are functions of one s:
#   s = e^(kx):  any R, Uⱼ;                 dx = ds/(k s)
#   s = cos kx, sin kx, tan kx: Bioche's invariances of R (as in `bioche`), Uⱼ invariant as functions
# then f dx = g(s, rⱼ) ds with rⱼ = Ũⱼ(s)^eⱼ, an algebraic integrand in s, integrated as such, and s put
# back. Both identities, g(s(θ))·s′ = R and Ũⱼ(s(θ)) = Uⱼ, are checked exactly in the tower (the rⱼ are
# constants there, so the check holds whatever branch the radicals take).
# ---------------------------------------------------------------------------

function integrate_monomial_radicals(f, x; build = nothing, lift = nothing, verify::Bool = true)
    @nospecialize f x
    # first the cheap derivative-divides test with a radicand as u (tanh⁵x sech^(3/4)x, u = sech x): the
    # substitution s = eˣ would give a 4th root of a degree-7 polynomial
    xk = string(x)
    bd0 = Builder(build === nothing ? auto_build(f, x) : build, lift === nothing ? auto_lift(f, x) : lift, x)
    if USUB_DEPTH[] < 2
        for (_, u) in unique(r -> string(r[2]), collect_radicals(f, xk))
            (isnode(u) && depends_on(u, xk) && radicand_element(u, xk) === nothing) || continue
            USUB_DEPTH[] += 1
            r = try
                integrate_usub(f, x, u, bd0; build = build, lift = lift, verify = verify)
            catch e
                # (DivideError: u′ is zero in the tower, u = sin²x + cos²x: not a substitution)
                (e isa RischNotImplemented || e isa NotElementary || e isa DivideError) || rethrow()
                nothing
            finally
                USUB_DEPTH[] -= 1
            end
            r === nothing || return r
        end
    end
    r = mr_direct(f, x; build = build, lift = lift, verify = verify)
    r === nothing || return r
    # radicands invariant under Bioche's involutions about π/4 (sin 2x = cos 2y): f(y + π/4), then y = x - π/4
    has_trig(t) = isnode(t) && (opname(operation(t)) in (:sin, :cos, :tan, :cot, :sec, :csc) || any(has_trig, arguments(t)))
    has_trig(f) || return nothing
    bd = Builder(build === nothing ? auto_build(f, x) : build, lift === nothing ? auto_lift(f, x) : lift, x)
    q4 = mk(bd, :/, bd.lift(π), bd.lift(4))
    # x ↦ x + c; a trig function of a linear argument a x + b becomes one of (a x + b) + a c, a sum that
    # `expand_trig_shifts` expands
    function shift(t, by)
        isnode(t) || return string(t) == xk ? mk(bd, :+, bd.x, by) : t
        args = arguments(t)
        if opname(operation(t)) in SHIFT_TRIG && length(args) == 1
            u = radicand_element(args[1], xk)
            if u !== nothing && isone(u.den) && degree(u.num) == 1
                a = u.num.c[2]
                return term_rebuild(bd, t, Any[mk(bd, :+, args[1], isone(a) ? by : mk(bd, :*, cterm(bd, a), by))])
            end
        end
        term_rebuild(bd, t, Any[shift(a, by) for a in args])
    end
    g = shift(f, q4)
    g2 = expand_trig_shifts(g, x, xk, build, lift)
    g2 === nothing && return nothing
    r = mr_direct(g2, x; build = build, lift = lift, verify = verify)
    r === nothing && return nothing
    shift(r, mk(bd, :*, bd.lift(-1), q4))
end

function mr_direct(f, x; build = nothing, lift = nothing, verify::Bool = true)
    @nospecialize f x
    xk = string(x)
    radt = Dict{String,Any}()                           # radical subterms with a non-rational radicand
    function findrads(t)
        isnode(t) || return
        rp = radical_parts(t)
        if rp !== nothing && depends_on(rp[2], xk) && radicand_element(rp[2], xk) === nothing
            isempty(collect_radicals(rp[2], xk)) || return     # (no radicals inside the radicand)
            radt[string(t)] = t
            return
        end
        foreach(findrads, arguments(t))
    end
    findrads(f)
    isempty(radt) && return nothing
    Us = Dict{String,Any}()                             # radicand elements, from the last parse
    function hook(t, T)
        haskey(radt, string(t)) && (Us[string(t)] = parse_tower(radical_parts(t)[2], T); return sym_const(T, t))
        rp = isnode(t) ? radical_parts(t) : nothing     # a constant radical (√2 from a shift): opaque
        (rp !== nothing && !depends_on(rp[2], xk)) && return sym_const(T, t)
        nothing
    end
    T, el = try
        build_tower(f, xk; subst = hook, minimize = false)
    catch e
        (e isa RischNotImplemented || e isa NeedComplex) && return nothing
        rethrow()
    end
    (length(T.levels) == 1 && T.levels[1].kind === :exp) || return nothing
    levelof(T, el) <= 1 || return nothing
    C = ctype(T)
    cs(p) = (v = [const_value(T, c) for c in p.c]; any(isnothing, v) ? nothing : UPoly{C}(C[c for c in v]))
    function tofrac(e)
        e = liftto(T, e, 1)
        N, Dn = cs(e.num), cs(e.den)
        (N === nothing || Dn === nothing) ? nothing : frac(N, Dn)
    end
    R = tofrac(el)
    R === nothing && return nothing
    Uθ = Dict{String,Any}()
    for (k, U) in Us
        u = tofrac(U)
        u === nothing && return nothing
        Uθ[k] = u
    end
    keys(Uθ) == keys(radt) || return nothing
    a = T.levels[1].arg                                 # θ = exp(a), a = c·x
    (isone(a.den) && degree(a.num) == 1 && iszero(a.num.c[1])) || return nothing
    cx = is_complex_field(C)
    P = UPoly{C}
    θp = xpoly(C)
    K1 = T.Ts[1]                                        # K₀; θ ∈ K₁ = K₀(θ)
    θel = frac(xpoly(K1))
    one1 = one(θel)
    li(c) = lconst(T, c, 1)
    two = cfromQ(C, Q(2))
    ca = a.num.c[2]                                     # θ = e^(ca·x)
    ev1(h) = foldr((c, acc) -> acc * θel + li(c), h.num.c; init = zero(θel)) /
             foldr((c, acc) -> acc * θel + li(c), h.den.c; init = zero(θel))
    pieces = Any[]                                      # (kind, g, tos, sel, piece of R)
    if !cx
        k = crational(ca)
        k === nothing && return nothing
        push!(pieces, (:exp, R * frac(P(C[one(C)]), scale(cfromQ(C, k), θp)), u -> u, θel, R))   # dx = ds/(k s)
    else
        I = cimag(C)
        kr = to_real(ca * inv(I))
        k = kr === nothing ? nothing : kr isa Q ? kr : crational(kr)
        k === nothing && return nothing
        U_ok(f) = all(u -> f(u) == u, values(Uθ))
        cosk(Rp) = (:cos, sym_to_s(Rp * frac(scale(-2 * I, θp), θp^2 - one(P))), u -> sym_to_s(u),
                    (θel + one1 / θel) * li(inv(two)), Rp)
        sink(Rp) = (:sin, sym_to_s(θscale(Rp * frac(scale(two, θp), θp^2 + one(P)), I)), u -> sym_to_s(θscale(u, I)),
                    (θel - one1 / θel) * li(inv(2 * I)), Rp)
        onep = frac(P(C[one(C), zero(C), one(C)]))
        tank(Rp) = (:tan, tan_to_s(Rp), u -> (v = tan_to_s(u); v === nothing ? nothing : v * onep),
                    li(-I) * (θel * θel - one1) / (θel * θel + one1), Rp)
        okc, oks, okt = U_ok(u -> θinv(u, one(C))), U_ok(u -> θinv(u, -one(C))), U_ok(u -> θscale(u, -one(C)))
        if θinv(R, one(C)) == -R && okc                 # s = cos kx
            push!(pieces, cosk(R))
        elseif θinv(R, -one(C)) == -R && oks            # s = sin kx
            push!(pieces, sink(R))
        elseif θscale(R, -one(C)) == R && okt           # s = tan kx
            push!(pieces, tank(R))
        elseif okc && oks && okt
            # Bioche's three involutions together: R dx = (cos piece) + (sin piece) + (tan piece), each
            # invariant for its substitution (the radicands are invariant under all three)
            h = inv(two)
            Rc = (R - θinv(R, one(C))) * kconst(h)
            rest = R - Rc
            Rs = (rest - θinv(rest, -one(C))) * kconst(h)
            Rt = rest - Rs
            iszero(Rc) || push!(pieces, cosk(Rc))
            iszero(Rs) || push!(pieces, sink(Rs))
            iszero(Rt) || push!(pieces, tank(Rt))
        else
            return nothing
        end
        pieces = Any[(kd, g === nothing ? nothing : g * kconst(inv(cfromQ(C, k))), tos, sel, Rp)
                     for (kd, g, tos, sel, Rp) in pieces]            # dx = du/k
    end
    RC = cx ? real_ctype(C) : C
    function real_frac(h)
        cx || return h
        n, d = [to_real(c) for c in h.num.c], [to_real(c) for c in h.den.c]
        (any(isnothing, n) || any(isnothing, d)) && return nothing
        frac(UPoly{RC}(RC[n...]), UPoly{RC}(RC[d...]))
    end
    bd = Builder(build === nothing ? auto_build(f, x) : build, lift === nothing ? auto_lift(f, x) : lift, x, T.consts)
    ut = isone(k) ? bd.x : mk(bd, :*, cterm(bd, k), bd.x)
    total = Any[]
    for (kind, g, tos, sel, Rp) in pieces
        g === nothing && return nothing
        Usx = Dict{String,Any}()
        for (kk, u) in Uθ
            v = tos(u)
            v === nothing && return nothing
            Usx[kk] = v
        end
        # exact checks: g(s(θ))·s′ = (the piece of) R and Ũⱼ(s(θ)) = Uⱼ
        gs(p) = foldr((c, acc) -> acc * sel + li(c), p.c; init = zero(sel))
        sub(h) = gs(h.num) / gs(h.den)
        sub(g) * D(T, 1, sel) == ev1(Rp) || throw(RischError("internal check failed: monomial substitution"))
        for (kk, v) in Usx
            sub(v) == liftto(T, Us[kk], 1) || throw(RischError("internal check failed: radicand in the substitution variable"))
        end
        gr = real_frac(g)
        gr === nothing && return nothing
        H = mr_piece(f, x, bd, T, radt, Usx, real_frac, RC, kind, gr; build = build, lift = lift, verify = verify)
        H === nothing && return nothing
        st = mk(bd, kind, ut)
        back(t) = isnode(t) ? term_rebuild(bd, t, Any[back(s) for s in arguments(t)]) : (string(t) == xk ? st : t)
        Hb = subst_answer(H, back, bd)
        Hb === nothing && return nothing
        push!(total, Hb)
    end
    add_answers(bd, total, xk)
end

# ∫ g(s) ds for one substitution of step MR: the radicals as terms in s (x stands for s), as generators of the
# constant field
function mr_piece(f, x, bd, T, radt, Usx, real_frac, RC, kind, gr; build, lift, verify)
    @nospecialize f x
    consts = copy(T.consts)
    for (kk, t) in radt
        j = findfirst(c -> c.kind === :sym && string(c.term) == kk, consts)
        j === nothing && return nothing
        v = real_frac(Usx[kk])
        v === nothing && return nothing
        e = radical_parts(t)[1]
        # s = e^(kx) > 0: (sᵐ w)^e = s^(me) w^e, the power of s taken out where me is an integer
        m = kind === :exp ? s_valuation(v) : 0
        me = m * e
        sm = 0
        if !iszero(m) && isone(denominator(me))
            sm = Int(numerator(me))
            v = v * frac(UPoly{RC}(RC[one(RC)]), xpoly(RC)^1)^m
        elseif !iszero(m)
            q = denominator(e)
            m2 = div(m, Int(q), RoundDown) * Int(q)           # the largest multiple of q in m
            if !iszero(m2)
                sm = Int(m2 * e)
                v = v * frac(UPoly{RC}(RC[one(RC)]), xpoly(RC)^1)^m2
            end
        end
        # a denominator D > 0 on ℝ (no real roots, positive leading coefficient): (N/D)^(p/q) = (N D^(q-1))^(p/q) / D^p
        dt = nothing
        if degree(v.den) > 0
            sg(c) = (r = crational(c); r !== nothing ? Int(sign(r)) : csign(c, T.consts))   # (ℚ(rⱼ, …): rational c)
            if real_root_count(v.den, nothing, nothing, sg) == 0 && sg(lc(v.den)) == 1
                q, pe = Int(denominator(e)), Int(numerator(e))
                dt = mk(bd, :^, poly_term(bd, v.den), bd.lift(pe))
                v = frac(v.num * v.den^(q - 1))
            end
        end
        ut = frac_term(bd, v)
        rt = isone(v) ? nothing : e == 1 // 2 ? mk(bd, :sqrt, ut) : mk(bd, :^, ut, bd.lift(e))
        dt === nothing || (rt = mk(bd, :/, rt === nothing ? bd.lift(1) : rt, dt))
        st = iszero(sm) ? nothing : isone(sm) ? bd.x : mk(bd, :^, bd.x, bd.lift(sm))
        consts[j] = ConstGen(:sym, Q(0), rt === nothing ? (st === nothing ? bd.lift(1) : st) :
                                              st === nothing ? rt : mk(bd, :*, st, rt))
    end
    bs = Builder(bd.build, bd.lift, x, consts)
    risch_integrate(frac_term(bs, gr), x; build = build, lift = lift, verify = verify)
end

# the order of s in h ∈ C(s): h = sᵐ·(unit at s = 0)
function s_valuation(h::Frac)
    v(p) = (i = findfirst(c -> !iszero(c), p.c); i === nothing ? 0 : i - 1)
    v(h.num) - v(h.den)
end

# ---------------------------------------------------------------------------
# Step PW: radicands that are perfect powers at a finer monomial. U = U(θ) with θ = e^(ckx) (or e^(ikx)) is,
# with θ = φ^q, U = r^q d W(φ)^q (1 + cos x = 2 cos²(x/2), 1 + sin x = (cos(x/2) + sin(x/2))², eˣ = (e^(x/2))²),
# W real, r ∈ ℚ or ℚ(i), d ≥ 1 squarefree (q = 2). W is built in the tower of φ and W^q = U checked there.
# f is integrated with U^(p/q) ↦ (√d W)^p, giving G. For q even and p odd, U^(p/q) = ±(√d W)^p with a sign
# constant where W keeps its sign: the answer G·U^(1/q)/(√d W) (Rubi's convention: -2cos x/√(1 + sin x)).
# One radicand only (all its exponents of one parity when q is even).
# ---------------------------------------------------------------------------
function integrate_power_radicands(f, x; build = nothing, lift = nothing, verify::Bool = true)
    @nospecialize f x
    xk = string(x)
    rads = Any[]
    function findrads(t)
        isnode(t) || return
        rp = radical_parts(t)
        if rp !== nothing && depends_on(rp[2], xk) && radicand_element(rp[2], xk) === nothing
            push!(rads, (t, rp...))
            return
        end
        foreach(findrads, arguments(t))
    end
    findrads(f)
    isempty(rads) && return nothing
    ut = rads[1][3]
    all(r -> string(r[3]) == string(ut), rads) || return nothing
    q = Int(lcm([denominator(r[2]) for r in rads]))
    ps = [Int(numerator(r[2] * q)) for r in rads]       # U^(p/q)
    iseven(q) && !(all(isodd, ps) || all(iseven, ps)) && return nothing
    T, U = try
        build_tower(ut, xk)
    catch e
        (e isa RischNotImplemented || e isa NeedComplex) && return nothing
        rethrow()
    end
    (length(T.levels) == 1 && T.levels[1].kind === :exp && levelof(T, U) == 1) || return nothing
    C = ctype(T)
    (C === Q || C === QI) || return nothing
    cs(p) = (v = [const_value(T, c) for c in p.c]; any(isnothing, v) ? nothing : UPoly{C}(C[c for c in v]))
    N, Dn = cs(U.num), cs(U.den)
    (N === nothing || Dn === nothing) && return nothing
    a = T.levels[1].arg                                 # θ = exp(ca x)
    (isone(a.den) && degree(a.num) == 1 && iszero(a.num.c[1])) || return nothing
    ca = a.num.c[2]
    kr = C === QI ? to_real(ca * inv(cimag(C))) : ca
    kr isa Q || return nothing
    # U(φ^q) = c P^q / Q^q
    up(p) = UPoly{C}(vcat((c -> vcat(c, fill(zero(C), q - 1))).(p.c)...))     # p(φ^q)
    function qpower(p)
        sf = squarefree(p)
        all(((_, m),) -> m % q == 0, sf) || return nothing
        P = one(p)
        for (g, m) in sf
            P = P * g^(m ÷ q)
        end
        lc(p), P
    end
    pn, pd = qpower(up(N)), qpower(up(Dn))
    (pn === nothing || pd === nothing) && return nothing
    c = pn[1] / pd[1]
    # c = r^q d
    r, d = nothing, 1
    if q == 2
        r = csqrt(c)
        if r === nothing
            if C === Q
                s0, d0 = sqfree_split(numerator(c) * denominator(c))
                d0 > 1 || return nothing
                r, d = Q(s0) / denominator(c), Int(d0)
            else
                sp = qi_split_sqrt(c)
                sp === nothing && return nothing
                d, r = sp
            end
        end
    elseif C === Q && c > 0
        rn, rd = round(BigInt, numerator(c)^(1 / q)), round(BigInt, denominator(c)^(1 / q))
        (rn^q == numerator(c) && rd^q == denominator(c)) || return nothing
        r = Q(rn, rd)
    else
        return nothing
    end
    # the tower of φ, from the term exp(ca/q x) (or sin of it) of the user's type
    bd = Builder(build === nothing ? auto_build(f, x) : build, lift === nothing ? auto_lift(f, x) : lift, x)
    kq = kr / q
    arg = isone(kq) ? bd.x : mk(bd, :*, cterm(bd, kq), bd.x)
    T2, φt = try
        build_tower(mk(bd, C === QI ? :sin : :exp, arg), xk; minimize = false)
    catch e
        (e isa RischNotImplemented || e isa NeedComplex) && return nothing
        rethrow()
    end
    length(T2.levels) == 1 || return nothing
    C2 = ctype(T2)
    C2 === C || return nothing
    K0 = T2.Ts[1]
    φ = frac(xpoly(K0))
    li(c) = lconst(T2, c, 1)
    ev(p) = foldr((cc, acc) -> acc * φ + li(cc), p.c; init = zero(φ))
    W = li(r) * ev(pn[2]) / ev(pd[2])
    Uφ = ev(up(N)) / ev(up(Dn))
    # (√d W)^q = U, d = 1 unless q = 2; a mismatch also catches a tower level other than e^(ca x/q)
    W^q * li(cfromQ(C, Q(d))) == Uφ || return nothing
    kinds = sigma_kinds(T2)
    if C === QI
        tconj(T2, kinds, W, 1) == W || return nothing  # W real
    end
    Wt = C === QI ? real_term(bd, T2, kinds, W) : tower_to_term(bd, T2, W)
    d == 1 || (Wt = mk(bd, :*, mk(bd, :sqrt, bd.lift(d)), Wt))
    pw(p) = p == 1 ? Wt : mk(bd, :^, Wt, bd.lift(p))
    pmap = Dict(string(t) => pw(p) for ((t, _, _), p) in zip(rads, ps))
    sub(t) = haskey(pmap, string(t)) ? pmap[string(t)] : isnode(t) ? term_rebuild(bd, t, Any[sub(s) for s in arguments(t)]) : t
    G = risch_integrate(sub(f), x; build = build, lift = lift, verify = verify)
    G isa IntegralWithRootSums && return nothing
    (iseven(q) && isodd(ps[1])) || return G
    root = q == 2 ? mk(bd, :sqrt, ut) : mk(bd, :^, ut, bd.lift(1 // q))
    H = mk(bd, :*, G, mk(bd, :/, root, Wt))
    (C === QI && q == 2) || return H
    corr = sign_jump_correction(bd, G, Wt, kq, xk)
    corr === nothing ? H : mk(bd, :+, H, corr)
end

# step PW's jumps: for q = 2 and p odd, H = G·√U/(√d W) = G·sign(W) jumps at the real zeros of W (√(1 + cos x):
# H = 2√2 sin(x/2) sign(cos(x/2)), by -4√2 at x = π, so ∫₀^2π gave 0). For W = a cos θ + b sin θ (θ = kq x;
# W = R cos(θ - δ), δ = atan2(b, a)) the zeros θₖ = δ + π/2 + kπ are evenly spaced, and when the jumps there are
# one J (G periodic, alternating in sign at the zeros), S = θ - atan((a sin θ - b cos θ)/(a cos θ + b sin θ)),
# θ - δ - atan(tan(θ - δ)) + δ, jumps by π at each: H - (J/π) S is continuous. J is taken numerically and
# recognized as r or r√d' (r a small rational, d' a small squarefree integer); nothing (H as it is) otherwise, as when
# the jumps grow (x√(1 + cos x)).
function sign_jump_correction(bd::Builder, G, Wt, kq::Q, xk::String)
    ev = numeric_evaluator(xk, G, Wt)
    rv(t, x0) = (v = try ev(t, x0) catch; return nothing end; abs(imag(v)) <= 1e-9 * max(1.0, abs(v)) ? real(v) : nothing)
    k = Float64(kq)
    a, b = rv(Wt, 0.0), rv(Wt, (π / 2) / k)
    (a === nothing || b === nothing) && return nothing
    # W = a cos θ + b sin θ (no constant, no higher harmonics)
    for θ in (0.37, 1.9, 4.4)
        w = rv(Wt, θ / k)
        (w !== nothing && abs(w - (a * cos(θ) + b * sin(θ))) <= 1e-9 * max(1.0, abs(a) + abs(b))) || return nothing
    end
    # a : b exactly (W's scale does not matter in the ratio)
    m = max(abs(a), abs(b))
    m > 0 || return nothing
    small(v) = (r = rationalize(v; tol = 1e-12); (denominator(r) <= 1000 && abs(r - v) <= 1e-10) ? Q(r) : nothing)
    aq, bq = small(a / m), small(b / m)
    (aq === nothing || bq === nothing) && return nothing
    δ = atan(b, a)
    # the jumps at four zeros: J = G(xₖ)·(sign of W after - before)
    Js = Float64[]
    for kk in -1:2
        x0 = (δ + π / 2 + kk * π) / k
        h = 1e-6 * max(1.0, abs(x0))
        g = rv(G, x0)
        (wl = rv(Wt, x0 - h); wr = rv(Wt, x0 + h))
        (g === nothing || wl === nothing || wr === nothing) && return nothing
        push!(Js, g * (sign(wr) - sign(wl)))
    end
    J = Js[1]
    all(j -> abs(j - J) <= 1e-8 * max(1.0, abs(J)), Js) || return nothing
    abs(J) <= 1e-12 && return nothing
    # J exactly: a rational, or a rational times √d' for a small squarefree d'
    Jt = nothing
    for d in (1, 2, 3, 5, 6, 7, 10)
        r = small(J / sqrt(d))
        r === nothing && continue
        Jt = d == 1 ? cterm(bd, r) : mk(bd, :*, cterm(bd, r), mk(bd, :sqrt, bd.lift(d)))
        break
    end
    Jt === nothing && return nothing
    θt = isone(kq) ? bd.x : mk(bd, :*, cterm(bd, kq), bd.x)
    sθ, cθ = mk(bd, :sin, θt), mk(bd, :cos, θt)
    lin(p, u, q, v) = (ts = Any[]; iszero(p) || push!(ts, isone(p) ? u : mk(bd, :*, cterm(bd, p), u));
                       iszero(q) || push!(ts, isone(q) ? v : mk(bd, :*, cterm(bd, q), v));
                       length(ts) == 1 ? ts[1] : mk(bd, :+, ts...))
    ratio = mk(bd, :/, lin(aq, sθ, -bq, cθ), lin(aq, cθ, bq, sθ))
    S = mk(bd, :+, θt, mk(bd, :*, bd.lift(-1), mk(bd, :atan, ratio)))
    mk(bd, :*, mk(bd, :*, bd.lift(-1), mk(bd, :/, Jt, bd.lift(π))), S)
end

# ---------------------------------------------------------------------------
# Step NR: nested radicals with an innermost radical of a linear radicand L = a x + b (√(1 + √(1 + x))):
# u = L^(1/Q), Q the lcm of the indices of L's radicals, x = (u^Q - b)/a, dx = Q u^(Q-1)/a du; L^(p/q) ↦ u^(pQ/q).
# The outer radicals then have radicands rational in u, integrated as usual; u = L^(1/Q) is put back.
# ---------------------------------------------------------------------------
function integrate_inner_linear_radical(f, x; build = nothing, lift = nothing, verify::Bool = true)
    @nospecialize f x
    xk = string(x)
    rads = collect_radicals(f, xk)
    nested = [(e, u) for (e, u) in rads if depends_on(u, xk) && !isempty(collect_radicals(u, xk))]
    # a linear radicand (coefficients may be parameters): (term, a, b, constants)
    function linear(v)
        T, ve = try
            build_tower(v, xk)
        catch err
            (err isa RischNotImplemented || err isa RischError) || rethrow()
            return nothing
        end
        (isempty(T.levels) && isone(ve.den) && degree(ve.num) == 1) || return nothing
        # (real coefficients: a + i a x would put i in x = (u^Q - b)/a, step CI)
        is_complex_field(ctype(T)) && any(c -> to_real(c) === nothing, ve.num.c) && return nothing
        (v, ve.num.c[2], ve.num.c[1], T.consts)
    end
    L = nothing
    for (_, u) in nested, (e2, v) in collect_radicals(u, xk)
        L = linear(v)
        L === nothing || break
    end
    if L === nothing && isempty(nested)
        # several radicands, one linear (√(a + bx)·√(c + dx)): u = √(linear) makes the others rational in u
        length(unique(string(u) for (_, u) in rads if depends_on(u, xk))) >= 2 || return nothing
        for (_, u) in rads
            depends_on(u, xk) || continue
            L = linear(u)
            L === nothing || break
        end
    end
    L === nothing && return nothing
    Lt, a, b0c, lconsts = L
    Q = Int(reduce(lcm, (denominator(e) for (e, u) in rads if string(u) == string(Lt)); init = 1))
    Q > 1 || return nothing
    bd = Builder(build === nothing ? auto_build(f, x) : build, lift === nothing ? auto_lift(f, x) : lift, x, lconsts)
    upow(k) = k == 1 ? bd.x : mk(bd, :^, bd.x, bd.lift(k))
    xu = mk(bd, :/, mk(bd, :+, upow(Q), cterm(bd, -b0c)), cterm(bd, a))     # x = (u^Q - b)/a
    function sub(t)
        if isnode(t)
            rp = radical_parts(t)
            (rp !== nothing && string(rp[2]) == string(Lt)) && return upow(Int(rp[1] * Q))
            return term_rebuild(bd, t, Any[sub(s) for s in arguments(t)])
        end
        string(t) == xk ? xu : t
    end
    g = mk(bd, :*, sub(f), mk(bd, :/, mk(bd, :*, bd.lift(Q), upow(Q - 1)), cterm(bd, a)))
    G = risch_integrate(g, x; build = build, lift = lift, verify = verify)
    root = Q == 2 ? mk(bd, :sqrt, Lt) : mk(bd, :^, Lt, bd.lift(1 // Q))
    back(t) = isnode(t) ? term_rebuild(bd, t, Any[back(s) for s in arguments(t)]) : (string(t) == xk ? root : t)
    subst_answer(G, back, bd)
end

# Step HT: radicals of trigonometric functions of one linear argument L = a x + b, after the other routes have
# refused them: t = tan(L/2), sin L = 2t/(1 + t²), cos L = (1 - t²)/(1 + t²), dx = 2 dt/(a (1 + t²)). Every
# radicand becomes a rational function of t with the same value (1 + sec x = 2/(1 - t²)), so its principal
# root is the same, and the integrand is algebraic in t; t = tan(L/2) is put back (an antiderivative on each
# interval between the poles of tan(L/2)). Nothing when x occurs outside the trigonometric functions, the
# arguments differ, or there is no radical of one.
const HT_TRIG = (:sin, :cos, :tan, :cot, :sec, :csc)
function integrate_halfangle_radicals(f, x; build = nothing, lift = nothing, verify::Bool = true)
    @nospecialize f x
    xk = string(x)
    args = Any[]
    function scan(t)                                    # the trigonometric arguments; false for x elsewhere
        safe_iscall(t) && !isempty(arguments(t)) || return string(t) != xk
        if opname(operation(t)) in HT_TRIG && length(arguments(t)) == 1 && has_x(arguments(t)[1], xk)
            push!(args, arguments(t)[1])
            return true
        end
        all(scan, arguments(t))
    end
    (scan(f) && !isempty(args)) || return nothing
    L = args[1]
    all(a -> string(a) == string(L), args) || return nothing
    any(((_, u),) -> any(n -> has_op(u, n), HT_TRIG), collect_radicals(f, xk)) || return nothing
    bd = Builder(build === nothing ? auto_build(f, x) : build, lift === nothing ? auto_lift(f, x) : lift, x)
    pp = poly_parts(bd, L, xk)
    (pp === nothing || !haskey(pp, 1) || maximum(keys(pp)) != 1) && return nothing
    a = pp[1]
    t = bd.x
    one_ = bd.lift(1)
    t2 = mk(bd, :^, t, bd.lift(2))
    S = mk(bd, :/, mk(bd, :*, bd.lift(2), t), mk(bd, :+, one_, t2))
    C = mk(bd, :/, mk(bd, :+, one_, mk(bd, :*, bd.lift(-1), t2)), mk(bd, :+, one_, t2))
    vals = Dict(:sin => S, :cos => C, :tan => mk(bd, :/, S, C), :cot => mk(bd, :/, C, S),
                :sec => mk(bd, :/, one_, C), :csc => mk(bd, :/, one_, S))
    walk(u) = !(safe_iscall(u) && !isempty(arguments(u))) ? u :
              (opname(operation(u)) in HT_TRIG && length(arguments(u)) == 1 && string(arguments(u)[1]) == string(L)) ?
              vals[opname(operation(u))] : term_rebuild(bd, u, Any[walk(s) for s in arguments(u)])
    g = mk(bd, :*, mk(bd, :/, bd.lift(2), mk(bd, :*, a, mk(bd, :+, one_, t2))), walk(f))
    G = risch_integrate(g, x; build = build, lift = lift, verify = verify)
    tL = mk(bd, :tan, mk(bd, :*, bd.lift(1 // 2), L))
    # the radicals of f in t (as the answer prints them) back to the radicals of f: √(1 + sec x), not its t form
    radmap = Dict{String,Any}()
    function radicals!(u)
        isnode(u) || return
        rp = radical_parts(u)
        rp !== nothing && has_x(rp[2], xk) && (radmap[string(walk(u))] = u)
        foreach(radicals!, arguments(u))
    end
    radicals!(f)
    back(u) = haskey(radmap, string(u)) ? radmap[string(u)] :
              isnode(u) ? term_rebuild(bd, u, Any[back(s) for s in arguments(u)]) : (string(u) == xk ? tL : u)
    subst_answer(G, back, bd)
end

# the one argument L of the trigonometric functions in f, when x appears only in them, else nothing
function single_trig_arg(f, xk::String)
    args = Any[]
    function scan(t)
        safe_iscall(t) && !isempty(arguments(t)) || return string(t) != xk
        if opname(operation(t)) in HT_TRIG && length(arguments(t)) == 1 && has_x(arguments(t)[1], xk)
            push!(args, arguments(t)[1])
            return true
        end
        all(scan, arguments(t))
    end
    (scan(f) && !isempty(args)) || return nothing
    Ls = string(args[1])
    all(a -> string(a) == Ls, args) ? args[1] : nothing
end
# the trigonometric function of L that u is (:sin, …, :csc), else nothing
function trig_of(u, Ls::String)
    (safe_iscall(u) && !isempty(arguments(u)) && opname(operation(u)) in HT_TRIG && length(arguments(u)) == 1 &&
     string(arguments(u)[1]) == Ls) ? opname(operation(u)) : nothing
end
# u -> u in t = tan L (the builder's variable), or nothing when u is not a rational function of tan L (step TQ)
function tan_walker(bd::Builder, Ls::String)
    t = bd.x
    one_ = bd.lift(1)
    W2 = mk(bd, :+, one_, mk(bd, :^, t, bd.lift(2)))
    pw(b, e) = e == 1 ? b : mk(bd, :^, b, bd.lift(e))
    function walk(u)
        (safe_iscall(u) && !isempty(arguments(u))) || return u
        leaf_rational(u) === nothing || return u                # (an exponent 5/2 kept, not 5 * 2^-1)
        n = opname(operation(u))
        if n === :+ || n === :-
            as = Any[walk(s) for s in arguments(u)]
            any(isnothing, as) && return nothing
            return term_rebuild(bd, u, as)
        end
        fs = product_factors!(Any[], u, 1)
        if length(fs) == 1 && fs[1][2] == 1 && fs[1][1] === u      # a call: tan, cot, a radical, …
            k = trig_of(u, Ls)
            k === :tan && return t
            k === :cot && return mk(bd, :/, one_, t)
            k === nothing || return nothing                         # sin, cos, sec, csc to an odd power
            as = Any[walk(s) for s in arguments(u)]
            any(isnothing, as) && return nothing
            return term_rebuild(bd, u, as)
        end
        w = 0
        parts = Any[]
        for (b, e) in fs
            k = trig_of(b, Ls)
            if k === :sin
                push!(parts, pw(t, e)); w -= e
            elseif k === :cos
                w -= e
            elseif k === :sec
                w += e
            elseif k === :csc
                push!(parts, pw(t, -e)); w += e
            else
                wb = walk(b)
                wb === nothing && return nothing
                push!(parts, pw(wb, e))
            end
        end
        isodd(w) && return nothing
        w == 0 || push!(parts, pw(W2, w ÷ 2))
        isempty(parts) ? one_ : length(parts) == 1 ? parts[1] : mk(bd, :*, parts...)
    end
end

# a square root (or its odd powers) of a + b tan L, a or b a parameter (param = true), L the one trigonometric argument
# of f: the radicals that step TQ takes before steps MR and HT
function tan_linear_radicand(e, u, f, x; param::Bool = true, deg::Int = 1)
    @nospecialize u f x
    xk = string(x)
    (denominator(e) == 2 && (has_op(u, :tan) || has_op(u, :cot)) && (!param || has_param(u, xk))) || return false
    L = single_trig_arg(f, xk)
    L === nothing && return false
    try
        bd = Builder(expr_build, identity, :t__)
        ut = tan_walker(bd, string(L))(u)
        ut === nothing && return false
        T, el = build_tower(ut, "t__")
        isempty(T.levels) && degree(el.den) == 0 && degree(el.num) == deg
    catch err
        (err isa RischNotImplemented || err isa RischError) || rethrow()
        false
    end
end

# two square roots of different radicands a + b tan L (step TR, parameters or not: √tan √(1 + tan) had a RootSum
# from step RM's merged quadratic radicand), or one linear in tan L with a parameter, or quadratic in tan L (step TQR:
# 1/√(2 + 3 tan + 5 tan²) had a quartic RootSum): step TQ first
tq_first(f, x, rads) = any(((e, u),) -> tan_linear_radicand(e, u, f, x) ||
                                        tan_linear_radicand(e, u, f, x; deg = 2, param = false), rads) ||
    length(unique(string(u) for (e, u) in rads if tan_linear_radicand(e, u, f, x; param = false))) >= 2

const TAN_ELLIPTIC_MSG = "a radicand of degree 3 or 4 in tan with a parameter, elliptic in general: not integrated"

# a power of a function of tan L or cot L with a symbolic exponent ((a + b tan(e + f x))ᵐ, tan(c + d x)ᵐ): step TQ's
# t = tan L first (the tower over ℚ(i)(a, …, m), tan L through exp(2iL), did not finish its Risch equations in
# minutes; over ℚ(a, …, m)(t) they decide in seconds), its answer or decision final
const TAN_SYMBOLIC_MSG = "a symbolic power of a function of tan, refused in t = tan: not integrated"
const TAN_SYMBOLIC_NE = "in t = tan: "
function tan_symbolic_power(t, xk::String)
    isnode(t) || return false
    args = arguments(t)
    if opname(operation(t)) === :^ && length(args) == 2 && !depends_on(args[2], xk) && leaf_rational(args[2]) === nothing &&
       has_symbol(args[2]) && (has_op(args[1], :tan) || has_op(args[1], :cot))
        return true
    end
    any(a -> tan_symbolic_power(a, xk), args)
end

# Step TQS: g = r(t) ρ (ρ the radicals of one radicand with a parameter, r ∈ ℚ(a, …)(t)) whose denominator has
# 1 + t² beside other factors H: r = P₁/(1 + t²)ᵐ + P₂/H, the two parts integrated apart. In u = √(a + b t),
# 1 + t² is the even quartic (u² - a)² + b² (step BQP), and the residues of H's factors are found alone, where
# those of the product over ℚ(a, b) were not (cot(c + d x)/√(a + b tan(c + d x))). The parts, or nothing.
function tan_split_parts(g, xk::String, bd::Builder)
    # (not over ℚ(i): 1 + t² = (1 + i t)(1 - i t) shares factors with the rest, and i, as I, would be a parameter)
    (has_imag_unit(g) || has_leaf(g, "I")) && return nothing
    rad, rest = Any[], Any[]
    for (b, e) in product_factors!(Any[], g, 1)
        rp = radical_parts(b)
        push!(rp !== nothing && has_x(rp[2], xk) ? rad : rest, (b, e))
    end
    isempty(rad) && return nothing
    us = string(radical_parts(rad[1][1])[2])
    all(((b, _),) -> string(radical_parts(b)[2]) == us, rad) || return nothing
    has_param(radical_parts(rad[1][1])[2], xk) || return nothing
    pw(b, e) = e == 1 ? b : mk(bd, :^, b, bd.lift(e))
    prod_(ts) = isempty(ts) ? bd.lift(1) : length(ts) == 1 ? ts[1] : mk(bd, :*, ts...)
    T, el = try
        build_tower(prod_(Any[pw(b, e) for (b, e) in rest]), xk)
    catch err
        (err isa RischNotImplemented || err isa RischError) || rethrow()
        return nothing
    end
    isempty(T.levels) || return nothing
    C = ctype(T)
    (C === Q || rational_tfield(C)) || return nothing
    P = UPoly{C}
    W = P(C[one(C), zero(C), one(C)])
    H, m = el.den, 0
    while degree(H) >= 2
        q, rm = divrem(H, W)
        iszero(rm) || break
        H, m = q, m + 1
    end
    (m > 0 && degree(H) > 0) || return nothing
    Wm = one(P)
    for _ in 1:m
        Wm = Wm * W
    end
    s, _, gg = gcdex(H, Wm)                            # s H + t Wᵐ = gg ∈ C
    degree(gg) == 0 || return nothing
    P1 = rem(el.num * s * P(C[inv(gg.c[1])]), Wm)
    P2, r2 = divrem(el.num - P1 * H, Wm)
    iszero(r2) || return nothing
    bt = Builder(bd.build, bd.lift, bd.x, T.consts)
    ρ = prod_(Any[pw(b, e) for (b, e) in rad])
    Any[mk(bt, :*, frac_term(bt, frac(p, d)), ρ) for (p, d) in ((P1, Wm), (P2, H)) if !iszero(p)]
end

# Step TQR: square roots of one radicand Q = a + b t + c t² (in t = tan L, step TQ; b ≠ 0), g = S(t)/√Q with S
# rational, split by partial fractions over its known factors t, 1 + t², Q:
#   (αt + β)/(1 + t²): from ∫ dt/((t - t₀)√Q) = -ln((2Q(t₀) + Q′(t₀)(t - t₀) + 2√Q(t₀)√Q)/(t - t₀))/√Q(t₀) at t₀ = i,
#     in real form with √Q(i) = √(a - c + ib) = P + iP′, P = √((r + a - c)/2), P′ = b/(2P), r = √((a - c)² + b²):
#     -((αP - βP′)/r) ½ ln((N₁² + N₂²)/(1 + t²)) - ((αP′ + βP)/r) atan((N₁ + N₂t)/(N₁t - N₂)),
#     N₁ = 2a + bt + 2P√Q, N₂ = b + 2ct + 2P′√Q (Rubi 4.3.9's nested √(a - c ± r));
#   1/tʲ: I₁ = -ln|(2a + bt + 2√a√Q)/t|/√a, I₀ = ln|b + 2ct + 2√c√Q|/√c, and from (√Q/tʲ⁻¹)′,
#     (j - 1) a Iⱼ = -√Q/tʲ⁻¹ + (3/2 - j) b Iⱼ₋₁ + (2 - j) c Iⱼ₋₂   (a, c > 0, the parameter convention);
#   the rest (a polynomial, powers of Q) by the usual route. The answer, or nothing (another power of 1 + t²).
function integrate_tan_quadratic_radical(g, x, bd::Builder; build = nothing, lift = nothing, verify::Bool = true)
    @nospecialize g x
    xk = string(x)
    U, E = nothing, Q(0)
    rest = Any[]
    for (b, e) in product_factors!(Any[], g, 1)
        rp = radical_parts(b)
        if rp !== nothing && has_x(rp[2], xk)
            denominator(rp[1]) == 2 || return nothing
            U === nothing && (U = rp[2])
            string(rp[2]) == string(U) || return nothing
            E += e * rp[1]
        else
            isempty(collect_radicals(b, xk)) || return nothing
            push!(rest, (b, e))
        end
    end
    (U === nothing || isinteger(E)) && return nothing
    pp = poly_parts(bd, U, xk)
    (pp === nothing || maximum(keys(pp)) != 2) && return nothing
    a, b, c = get(pp, 0, bd.lift(0)), get(pp, 1, bd.lift(0)), pp[2]
    (leaf_rational(a) == 0 || leaf_rational(b) == 0) && return nothing
    pw(t, e) = e == 1 ? t : mk(bd, :^, t, bd.lift(e))
    k = Int(E + Q(1) // 2)
    fs = Any[pw(t, e) for (t, e) in rest]
    k == 0 || push!(fs, pw(U, k))
    St = isempty(fs) ? bd.lift(1) : length(fs) == 1 ? fs[1] : mk(bd, :*, fs...)
    # (one field for S and Q: the tower of S + Q has the constants of both)
    T, el, Up = try
        T, _ = build_tower(mk(bd, :+, St, U), xk)
        T, parse_tower(St, T), parse_tower(U, T)
    catch err
        (err isa RischNotImplemented || err isa RischError || err isa NewConstants || err isa Restart) || rethrow()
        return nothing
    end
    isempty(T.levels) || return nothing
    C = ctype(T)
    (C === Q || rational_tfield(C)) || return nothing
    P = UPoly{C}
    X = P(C[zero(C), one(C)])
    W = P(C[one(C), zero(C), one(C)])
    isone(Up.den) || return nothing
    parts0 = known_factor_parts(el, P[X, W, monic(Up.num)])
    parts0 === nothing && return nothing
    # (a part with the polynomial part of el, a lone factor's: that polynomial apart, by the usual route)
    parts = Frac{P}[]
    for φ in parts0
        qq, rr = divrem(φ.num, φ.den)
        iszero(qq) || degree(φ.den) == 0 || push!(parts, frac(qq))
        push!(parts, degree(φ.den) == 0 ? φ : frac(rr, φ.den))
    end
    filter!(φ -> !iszero(φ), parts)
    bt = Builder(bd.build, bd.lift, bd.x, T.consts)
    t = bd.x
    neg(v) = mk(bd, :*, bd.lift(-1), v)
    sq(v) = mk(bd, :sqrt, v)
    sQ = sq(U)
    co(p, i) = i <= length(p.c) ? p.c[i] : zero(C)
    out = Any[]
    Is = Dict{Int,Any}()
    function I(j)
        haskey(Is, j) && return Is[j]
        # (½ ln(u²) for ln|u|: (2a + bt + 2√a√Q)/t changes sign with t, b + 2ct + 2√c√Q where b² > 4ac)
        lnabs(u) = mk(bd, :*, bd.lift(1 // 2), mk(bd, :log, pw(u, 2)))
        v = if j == 0
            mk(bd, :/, lnabs(mk(bd, :+, b, mk(bd, :*, bd.lift(2), c, t), mk(bd, :*, bd.lift(2), sq(c), sQ))), sq(c))
        elseif j == 1
            neg(mk(bd, :/, lnabs(mk(bd, :/, mk(bd, :+, mk(bd, :*, bd.lift(2), a), mk(bd, :*, b, t),
                                                    mk(bd, :*, bd.lift(2), sq(a), sQ)), t)), sq(a)))
        else
            num = mk(bd, :+, neg(mk(bd, :/, sQ, pw(t, j - 1))), mk(bd, :*, bd.lift(Q(3) // 2 - j), b, I(j - 1)),
                     mk(bd, :*, bd.lift(2 - j), c, I(j - 2)))
            mk(bd, :/, num, mk(bd, :*, bd.lift(j - 1), a))
        end
        Is[j] = v
    end
    for φ in parts
        D = φ.den
        if D == W
            αc, βc = co(φ.num, 2), co(φ.num, 1)
            two = bd.lift(2)
            # u p + v q, the zero coefficients left out
            function comb(u, p, v, q)
                ts = Any[]
                iszero(u) || push!(ts, isone(u) ? p : mk(bd, :*, cterm(bt, u), p))
                iszero(v) || push!(ts, isone(v) ? q : mk(bd, :*, cterm(bt, v), q))
                length(ts) == 1 ? ts[1] : mk(bd, :+, ts...)
            end
            r = sq(mk(bd, :+, pw(mk(bd, :+, a, neg(c)), 2), pw(b, 2)))
            Pr = sq(mk(bd, :/, mk(bd, :+, r, a, neg(c)), two))
            P2 = mk(bd, :/, b, mk(bd, :*, two, Pr))
            N1 = mk(bd, :+, mk(bd, :*, two, a), mk(bd, :*, b, t), mk(bd, :*, two, Pr, sQ))
            N2 = mk(bd, :+, b, mk(bd, :*, two, c, t), mk(bd, :*, two, P2, sQ))
            L = mk(bd, :*, bd.lift(1 // 2), mk(bd, :log, mk(bd, :/, mk(bd, :+, pw(N1, 2), pw(N2, 2)), mk(bd, :+, bd.lift(1), pw(t, 2)))))
            Θ = mk(bd, :atan, mk(bd, :/, mk(bd, :+, N1, mk(bd, :*, N2, t)), mk(bd, :+, mk(bd, :*, N1, t), neg(N2))))
            k1 = mk(bd, :/, comb(αc, Pr, -βc, P2), r)
            k2 = mk(bd, :/, comb(αc, P2, βc, Pr), r)
            push!(out, neg(mk(bd, :+, mk(bd, :*, k1, L), mk(bd, :*, k2, Θ))))
        elseif degree(D) >= 1 && D == X^degree(D)
            kk = degree(D)
            for j in 1:kk
                p = co(φ.num, kk - j + 1)                   # p_{k-j}/tʲ
                iszero(p) || push!(out, mk(bd, :*, cterm(bt, p), I(j)))
            end
        elseif degree(D) >= 2 && any(m -> D == W^m, 2:degree(D))
            return nothing
        else
            # Qᵐ of the denominator into the power of the radical: P Q^(-m - 1/2) (the route refuses P/Q beside 1/√Q)
            Uq = monic(Up.num)
            m, Dr = 0, D
            while degree(Dr) >= degree(Uq)
                qq, rr = divrem(Dr, Uq)
                iszero(rr) || break
                Dr, m = qq, m + 1
            end
            ψ = m == 0 ? φ : frac(φ.num * P(C[lc(Up.num)^m]), Dr)     # (D = Dr (Q/lc)ᵐ)
            G = try
                risch_integrate(mk(bd, :*, frac_term(bt, ψ), mk(bd, :^, U, bd.lift(-m - 1 // 2))), x; build = build, lift = lift,
                                verify = verify)
            catch err
                (err isa RischNotImplemented || err isa NotElementary) || rethrow()
                return nothing
            end
            G isa IntegralWithRootSums && return nothing
            push!(out, G)
        end
    end
    isempty(out) ? nothing : length(out) == 1 ? out[1] : mk(bd, :+, out...)
end

# Step TR: square roots of two radicands L₁ = a₁ + b₁t, L₂ = a₂ + b₂t (in t = tan L, step TQ) to odd powers:
# √L₁^(2k₁+1) √L₂^(2k₂+1) = L₁^k₁ L₂^(k₂+1) u with u = √L₁/√L₂, exactly on every branch ((√L₂)² = L₂).
# t = (a₁ - a₂u²)/(b₂u² - b₁), dt = 2u(a₂b₁ - a₁b₂)/(b₂u² - b₁)² du make the integrand rational in u. Its
# denominator's factors are known (u, b₂u² - b₁ for t = ∞, and the images of the rest's factors: 1 + t² gives the
# even quartic (a₁ - a₂u²)² + (b₂u² - b₁)², step BQP), so it is split by partial fractions over ℚ(a, …) without
# factoring there, and each part integrated alone; u = √L₁/√L₂ is put back. Rubi 4.3.2.1 √tan (a + b tan)^(5/2),
# (a + b tan)^(3/2)/(c + d tan)^(3/2). The answer, or nothing.
function integrate_two_linear_radicals(g, x, bd::Builder; build = nothing, lift = nothing, verify::Bool = true)
    @nospecialize g x
    xk = string(x)
    rads = Dict{String,Tuple{Any,Q}}()
    rest = Any[]
    σs = Any[]                                                # √(1/M) √M = ±1 for each odd power of √(1/M)
    for (b, e) in product_factors!(Any[], g, 1)
        rp = radical_parts(b)
        if rp !== nothing && has_x(rp[2], xk)
            denominator(rp[1]) == 2 || return nothing
            R, E = rp[2], e * rp[1]
            # a radicand 1/M (√cot = √(1/t)): (1/M)^E = σ M^(-E) with σ = √(1/M) √M, constant ±1 on intervals
            if safe_iscall(R) && opname(operation(R)) === :/ && length(arguments(R)) == 2 &&
               leaf_rational(arguments(R)[1]) == 1
                M = arguments(R)[2]
                isodd(numerator(2E)) && push!(σs, mk(bd, :*, mk(bd, :sqrt, R), mk(bd, :sqrt, M)))
                R, E = M, -E
            end
            k = string(R)
            rads[k] = (R, get(rads, k, (R, Q(0)))[2] + E)
        else
            isempty(collect_radicals(b, xk)) || return nothing
            push!(rest, (b, e))
        end
    end
    length(rads) == 2 || return nothing
    (L1, E1), (L2, E2) = sort(collect(values(rads)); by = r -> string(r[1]))
    (isinteger(E1) || isinteger(E2)) && return nothing        # (one odd radical: one radicand, step TQ)
    lin(L) = (pp = poly_parts(bd, L, xk); (pp === nothing || maximum(keys(pp)) != 1) ? nothing :
              (get(pp, 0, bd.lift(0)), pp[1]))
    c1, c2 = lin(L1), lin(L2)
    (c1 === nothing || c2 === nothing) && return nothing
    (a1, b1), (a2, b2) = c1, c2
    u = bd.x
    neg(t) = mk(bd, :*, bd.lift(-1), t)
    u2 = mk(bd, :^, u, bd.lift(2))
    den = mk(bd, :+, mk(bd, :*, b2, u2), neg(b1))              # b₂u² - b₁
    tu = mk(bd, :/, mk(bd, :+, a1, neg(mk(bd, :*, a2, u2))), den)
    sub(t) = isnode(t) ? term_rebuild(bd, t, Any[sub(a) for a in arguments(t)]) : (string(t) == xk ? tu : t)
    pw(b, e) = e == 1 ? b : mk(bd, :^, b, bd.lift(e))
    k1, k2 = Int(E1 - Q(1) // 2), Int(E2 - Q(1) // 2)
    dt = mk(bd, :/, mk(bd, :*, bd.lift(2), u, mk(bd, :+, mk(bd, :*, a2, b1), neg(mk(bd, :*, a1, b2)))), pw(den, 2))
    fs = Any[pw(sub(b), e) for (b, e) in rest]
    k1 == 0 || push!(fs, pw(sub(L1), k1))
    k2 + 1 == 0 || push!(fs, pw(sub(L2), k2 + 1))
    push!(fs, u, dt)
    gu = mk(bd, :*, fs...)
    T, el = try
        build_tower(gu, xk)
    catch err
        (err isa RischNotImplemented || err isa RischError) || rethrow()
        return nothing
    end
    isempty(T.levels) || return nothing
    C = ctype(T)
    cx = is_complex_field(C)
    (C === Q || rational_tfield(C) || cx) || return nothing
    P = UPoly{C}
    # the known factors, in the field of el
    cands = P[P(C[zero(C), one(C)])]
    for t in Any[den, (sub(b) for (b, e) in rest if e < 0)...]
        φ = try
            parse_tower(t, T)
        catch err
            (err isa RischNotImplemented || err isa RischError || err isa NewConstants || err isa Restart) || rethrow()
            return nothing
        end
        for q in (φ.num, φ.den)
            degree(q) > 0 && push!(cands, monic(q))
        end
    end
    parts = known_factor_parts(el, cands)
    parts === nothing && return nothing
    bt = Builder(bd.build, bd.lift, bd.x, T.consts)
    Gs = Any[]
    # over ℚ(i)(…) (√tan beside (a + i a tan)^(5/2), Rubi 4.3 4:470): each part as g_re + i g_im, real rational
    # functions of u integrated apart; their real forms continue analytically to the complex u (as in step LC)
    integ(h) = try
        F = risch_integrate(h, x; build = build, lift = lift, verify = verify)
        F isa IntegralWithRootSums ? nothing : F
    catch err
        (err isa RischNotImplemented || err isa NotElementary) || rethrow()
        nothing
    end
    cj(p) = P(C[cconj_g(T.consts, c) for c in p.c])
    for φ in parts
        if cx
            # φ = φ_re + i φ_im with φ_re = (φ + σφ)/2, φ_im = (φ - σφ)/(2i) (σ: i ↦ -i on the coefficients)
            σφ = frac(cj(φ.num), cj(φ.den))
            two = cfromQ(C, Q(2))
            re = (φ + σφ) * frac(P(C[inv(two)]))
            imp = (φ - σφ) * frac(P(C[inv(two * cimag(C))]))
            hr = iszero(re) ? nothing : frac_term(bt, re)
            hi = iszero(imp) ? nothing : frac_term(bt, imp)
            Gr = hr === nothing ? nothing : integ(hr)
            Gi = hi === nothing ? nothing : integ(hi)
            ((hr !== nothing && Gr === nothing) || (hi !== nothing && Gi === nothing)) && return nothing
            ts = Any[]
            Gr === nothing || push!(ts, Gr)
            Gi === nothing || push!(ts, mk(bd, :*, bd.lift(im), Gi))
            isempty(ts) || push!(Gs, length(ts) == 1 ? ts[1] : mk(bd, :+, ts...))
        else
            G = integ(frac_term(bt, φ))
            G === nothing && return nothing
            push!(Gs, G)
        end
    end
    isempty(Gs) && return nothing
    G = length(Gs) == 1 ? Gs[1] : mk(bd, :+, Gs...)
    ub = mk(bd, :/, mk(bd, :sqrt, L1), mk(bd, :sqrt, L2))
    back(t) = isnode(t) ? term_rebuild(bd, t, Any[back(a) for a in arguments(t)]) : (string(t) == xk ? ub : t)
    G = back(G)
    isempty(σs) ? G : mk(bd, :*, σs..., G)
end

# el = Σ Pᵢ/Fᵢ^mᵢ (+ a polynomial in the last part) for the factors Fᵢ of el's denominator among `cands` (pairwise
# coprime; what is left of the denominator is one more factor): the parts (el alone for one factor), or nothing
# (cands not coprime)
function known_factor_parts(el::Frac{UPoly{C}}, cands) where {C}
    P = UPoly{C}
    D = el.den
    facs = Tuple{P,Int}[]
    for F in cands
        any(((G, _),) -> G == F, facs) && continue
        m = 0
        while degree(D) >= degree(F)
            q, r = divrem(D, F)
            iszero(r) || break
            D, m = q, m + 1
        end
        m > 0 && push!(facs, (F, m))
    end
    degree(D) > 0 && push!(facs, (monic(D), 1))
    length(facs) <= 1 && return Frac{P}[el]                    # (one factor: el whole)
    N = el.num * P(C[inv(lc(el.den))])
    Drest = one(P)
    for (F, m) in facs, _ in 1:m
        Drest = Drest * F
    end
    parts = Frac{P}[]
    for (F, m) in facs[1:end-1]
        Fm = one(P)
        for _ in 1:m
            Fm = Fm * F
        end
        H = quo(Drest, Fm)
        s, _, gg = gcdex(H, Fm)
        degree(gg) == 0 || return nothing
        P1 = rem(N * s * P(C[inv(gg.c[1])]), Fm)
        N, r = divrem(N - P1 * H, Fm)
        iszero(r) || return nothing
        iszero(P1) || push!(parts, frac(P1, Fm))
        Drest = H
    end
    iszero(N) || push!(parts, frac(N, Drest))
    parts
end

# Step TQ: radicals of a + b tan(L) (L = a x + b, as in step HT) by t = tan(L) itself, when the rest of the integrand
# is a rational function of tan L (Bioche: invariant under L ↦ L + π): tan → t, cot → 1/t, and in each product
# sinʲ cosᵏ secˡ cscᵐ with j + k - l - m even, sin = t w⁻¹, cos = w⁻¹, w = √(1 + t²), so the w's give (1 + t²)^(integer);
# dx = dt/(a (1 + t²)). The radicand stays linear in t: √(1 + i t) is step LC's, where step HT's t = tan(L/2) made it
# a quadratic over ℚ(i), which no step takes (cot(c + d x)² √(a + i a tan(c + d x)), cos⁴/(a + i a tan)^(3/2)).
# t = tan(L) is put back (an antiderivative on each interval between the poles of tan L).
function integrate_tan_radicals(f, x; build = nothing, lift = nothing, verify::Bool = true, radicals::Bool = true)
    @nospecialize f x
    xk = string(x)
    L = single_trig_arg(f, xk)
    L === nothing && return nothing
    Ls = string(L)
    (!radicals || any(((_, u),) -> has_op(u, :tan) || has_op(u, :cot), collect_radicals(f, xk))) || return nothing
    bd = Builder(build === nothing ? auto_build(f, x) : build, lift === nothing ? auto_lift(f, x) : lift, x)
    pp = poly_parts(bd, L, xk)
    (pp === nothing || !haskey(pp, 1) || maximum(keys(pp)) != 1) && return nothing
    a = pp[1]
    t = bd.x
    one_ = bd.lift(1)
    W2 = mk(bd, :+, one_, mk(bd, :^, t, bd.lift(2)))
    walk = tan_walker(bd, Ls)
    ft = walk(f)
    ft === nothing && return nothing
    g = mk(bd, :/, ft, mk(bd, :*, a, W2))
    G = integrate_tan_quadratic_radical(g, x, bd; build = build, lift = lift, verify = verify)
    G === nothing && (G = integrate_two_linear_radicals(g, x, bd; build = build, lift = lift, verify = verify))
    parts = G === nothing ? tan_split_parts(g, xk, bd) : nothing
    if parts !== nothing
        Gs = try
            Any[risch_integrate(h, x; build = build, lift = lift, verify = verify) for h in parts]
        catch e
            e isa RischNotImplemented || rethrow()
            nothing
        end
        (Gs === nothing || any(F -> F isa IntegralWithRootSums, Gs)) || (G = mk(bd, :+, Gs...))
    end
    G === nothing && (G = risch_integrate(g, x; build = build, lift = lift, verify = verify))
    tL = mk(bd, :tan, L)
    radmap = Dict{String,Any}()
    function radicals!(u)
        isnode(u) || return
        rp = radical_parts(u)
        if rp !== nothing && has_x(rp[2], xk)
            wu = walk(u)
            wu === nothing || (radmap[string(wu)] = u)
        end
        foreach(radicals!, arguments(u))
    end
    radicals!(f)
    back(u) = haskey(radmap, string(u)) ? radmap[string(u)] :
              isnode(u) ? term_rebuild(bd, u, Any[back(s) for s in arguments(u)]) : (string(u) == xk ? tL : u)
    subst_answer(G, back, bd)
end

# Step TS: products of powers of sec L (odd, or a radical of e sec L, e cos L) and radicals of a ± i a tan L, the rest
# rational in tan L. With t = tan L, w = 1 + i t, w̄ = 1 - i t, sec² L = w w̄ exactly, and each radical ρ = B^(1/q) of the
# integrand has an exponent vector in (w, w̄) (sec ↦ (½, ½), a + i a t ↦ (1, 0), a - i a t ↦ (0, 1)), the integrand's
# radicals together (P, Q). When P, Q or P + Q is an integer (Chebyshev: else the integral is not elementary,
# √(e sec L) (a + i a tan L) is elliptic), one product V of the radicals (and sec L, w, w̄, constants) has V^N equal to
# w̄, w or w/w̄ exactly, and the integrand is M · R(t) Vʲ with R rational and M a product of the radicals whose
# exponent vector is 0: Mᴷ is a constant, so M is constant on intervals. ∫ R(t) Y^(j/N) dt (Y = w̄, w, w/w̄: one
# linear or Möbius radicand over ℚ(i), step LC) is then put back with Y^(1/N) ↦ V and t ↦ tan L; V, not the
# principal root of Y, keeps the answer an antiderivative where sec L < 0 (Rubi 4.3.1.2 sec³ (a + i a tan)^(3/2),
# (e sec)^(5/2) (a + i a tan)^(3/2), 1/((e cos)^(7/2) √(a + i a tan))).
function integrate_sec_tan_radicals(f, x; build = nothing, lift = nothing, verify::Bool = true)
    @nospecialize f x
    xk = string(x)
    L = single_trig_arg(f, xk)
    L === nothing && return nothing
    Ls = string(L)
    I_ = find_imag_unit(f)
    I_ === nothing && return nothing
    bd = Builder(build === nothing ? auto_build(f, x) : build, lift === nothing ? auto_lift(f, x) : lift, x)
    pp = poly_parts(bd, L, xk)
    (pp === nothing || !haskey(pp, 1) || maximum(keys(pp)) != 1) && return nothing
    aL = pp[1]
    t = bd.x
    one_ = bd.lift(1)
    walk = tan_walker(bd, Ls)
    pw(b, e) = isone(e) ? b : mk(bd, :^, b, bd.lift(e))
    w = mk(bd, :+, one_, mk(bd, :*, I_, t))
    wb = mk(bd, :+, one_, mk(bd, :*, bd.lift(-1), I_, t))
    tL = mk(bd, :tan, L)
    wL = mk(bd, :+, one_, mk(bd, :*, I_, tL))                 # (w, w̄ in x, for V and M)
    wbL = mk(bd, :+, one_, mk(bd, :*, bd.lift(-1), I_, tL))
    ev = numeric_evaluator(xk, f)
    # a base B of a radical: (constant factors, exponent vector) with B = Π constants · sec^k · (α ± i α tan)^m
    function base_vector(B)
        cs = Any[]
        v = (Q(0), Q(0))
        for (b, e) in product_factors!(Any[], B, 1)
            if !has_x(b, xk)
                leaf_rational(b) == 1 || push!(cs, pw(b, e))
                continue
            end
            k = trig_of(b, Ls)
            if k === :sec || k === :cos
                h = Q(k === :sec ? e : -e) // 2
                v = (v[1] + h, v[2] + h)
                continue
            end
            k === nothing || return nothing
            safe_iscall(b) && opname(operation(b)) in (:+, :-) || return nothing
            bt = walk(b)
            bt === nothing && return nothing
            lp = poly_parts(bd, bt, xk)
            (lp === nothing || sort(collect(keys(lp))) != [0, 1]) && return nothing
            α, β = lp[0], lp[1]
            z = try
                ev(β, 0.0) / ev(α, 0.0)
            catch
                return nothing
            end
            if abs(z - im) < 1e-10
                v = (v[1] + e, v[2])
            elseif abs(z + im) < 1e-10
                v = (v[1], v[2] + e)
            else
                return nothing
            end
            leaf_rational(α) == 1 || push!(cs, pw(α, e))
        end
        cs, v
    end
    rads = Any[]                  # (ρ = B^(1/q), q, power p of ρ in f, vector of ρ, constant of B)
    sw = 0                        # the power of sec L in f
    rest = Any[]                  # the rest of f in t
    consts = Any[]
    for (b, e) in product_factors!(Any[], f, 1)
        if !has_x(b, xk)
            leaf_rational(b) == 1 || push!(consts, pw(b, e))
            continue
        end
        k = trig_of(b, Ls)
        if k === :sin
            push!(rest, pw(t, e)); sw -= e
        elseif k === :cos
            sw -= e
        elseif k === :sec
            sw += e
        elseif k === :csc
            push!(rest, pw(t, -e)); sw += e
        else
            rp = radical_parts(b)
            if rp !== nothing && has_x(rp[2], xk)
                bv = base_vector(rp[2])
                bv === nothing && return nothing
                r = rp[1] * e
                q = Int(denominator(rp[1]))
                v = (bv[2][1] / q, bv[2][2] / q)
                push!(rads, (pw(rp[2], Q(1) // q), q, Int(numerator(rp[1])) * e, v, bv[1]))
            else
                bt = walk(b)
                bt === nothing && return nothing
                push!(rest, pw(bt, e))
            end
        end
    end
    # (else step TQ's: even powers of sec L, radicals of a ± i a tan L alone)
    (isodd(sw) || any(r -> !iszero(r[4][1]) && !iszero(r[4][2]), rads)) || return nothing
    P = sum(r[3] * r[4][1] for r in rads; init = Q(sw) // 2)
    Qv = sum(r[3] * r[4][2] for r in rads; init = Q(sw) // 2)
    isint(c) = isone(denominator(c))
    d, N = if isint(P) && isint(Qv)
        (Q(0), Q(0)), 1
    elseif isint(P)
        (Q(0), Q(1) // denominator(Qv)), Int(denominator(Qv))
    elseif isint(Qv)
        (Q(1) // denominator(P), Q(0)), Int(denominator(P))
    elseif isint(P + Qv)
        (Q(1) // denominator(P), -Q(1) // denominator(P)), Int(denominator(P))
    else
        return nothing
    end
    # V = Π ρₖ^eₖ secᵉ⁰ w^(-h₁) w̄^(-h₂) with vector d, Vᴺ a rational function of t (eₖ N/qₖ, e₀ N integers, e₀ N even)
    gens = Any[(r[1], r[2], r[4], r[5]) for r in rads]
    push!(gens, (mk(bd, :sec, L), 2, (Q(1) // 2, Q(1) // 2), Any[]))
    best = nothing
    if N > 1
        ranges = [(-(g[2] - 1)):(g[2] - 1) for g in gens]
        for es in Iterators.product(ranges...)
            all(k -> isint(Q(es[k] * N) // gens[k][2]), eachindex(gens)) || continue
            v = (sum(es[k] * gens[k][3][1] for k in eachindex(gens)), sum(es[k] * gens[k][3][2] for k in eachindex(gens)))
            (isint(v[1] - d[1]) && isint(v[2] - d[2])) || continue
            c = 4 * sum(abs, es) + abs(Int(v[1] - d[1])) + abs(Int(v[2] - d[2]))
            (best === nothing || c < best[1]) && (best = (c, es, (Int(v[1] - d[1]), Int(v[2] - d[2]))))
        end
        best === nothing && return nothing
    end
    # V′ = V · Π cₖ^(-eₖ/qₖ) (the constants of the bases out, principal powers: V′ᴺ = Y exactly)
    Vf = Any[]
    if N > 1
        es, h = best[2], best[3]
        for (k, g) in enumerate(gens)
            iszero(es[k]) && continue
            push!(Vf, pw(g[1], es[k]))
            for c in g[4]
                leaf_rational(c) == 1 || push!(Vf, pw(c, -Q(es[k]) // g[2]))
            end
        end
        h[1] == 0 || push!(Vf, pw(wL, -h[1]))
        h[2] == 0 || push!(Vf, pw(wbL, -h[2]))
    end
    V = isempty(Vf) ? one_ : length(Vf) == 1 ? Vf[1] : mk(bd, :*, Vf...)
    Y = d[2] == 0 ? w : d[1] == 0 ? wb : mk(bd, :/, w, wb)
    j = N == 1 ? 0 : Int(N * (iszero(d[1]) ? Qv : P))
    a0, b0 = Int(P - j * d[1]), Int(Qv - j * d[2])
    # M = (radicals of f) / (V′ʲ wᵃ⁰ w̄ᵇ⁰): exponent vector 0
    Mn = Any[pw(r[1], r[3]) for r in rads]
    sw == 0 || push!(Mn, pw(mk(bd, :sec, L), sw))
    Md = Any[]
    j == 0 || push!(Md, pw(V, j))
    a0 == 0 || push!(Md, pw(wL, a0))
    b0 == 0 || push!(Md, pw(wbL, b0))
    prodt(v) = isempty(v) ? one_ : length(v) == 1 ? v[1] : mk(bd, :*, v...)
    M = mk(bd, :/, prodt(vcat(consts, Mn)), leaf_rational(aL) == 1 ? prodt(Md) : mk(bd, :*, aL, prodt(Md)))
    gpart = Any[rest...]
    a0 == 0 || push!(gpart, pw(w, a0))
    b0 == 0 || push!(gpart, pw(wb, b0))
    j == 0 || push!(gpart, pw(Y, Q(j) // N))
    g = mk(bd, :/, prodt(gpart), mk(bd, :+, one_, mk(bd, :^, t, bd.lift(2))))
    G = risch_integrate(g, x; build = build, lift = lift, verify = verify)
    Ys = string(Y)
    function back(u)
        isnode(u) || return string(u) == xk ? tL : u
        rp = radical_parts(u)
        (rp !== nothing && string(rp[2]) == Ys) && return pw(V, rp[1] * N)
        term_rebuild(bd, u, Any[back(s) for s in arguments(u)])
    end
    H = subst_answer(G, back, bd)
    H === nothing && return nothing
    H isa IntegralWithRootSums && return nothing
    mk(bd, :*, M, H)
end
