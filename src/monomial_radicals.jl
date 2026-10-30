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
    mk(bd, :*, G, mk(bd, :/, root, Wt))
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
        (isempty(T.levels) && isone(ve.den) && degree(ve.num) == 1) ? (v, ve.num.c[2], ve.num.c[1], T.consts) : nothing
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
