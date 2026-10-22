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
    hook(t, T) = haskey(radt, string(t)) ?
        (Us[string(t)] = parse_tower(radical_parts(t)[2], T); sym_const(T, t)) : nothing
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
    if !cx
        k = crational(ca)
        k === nothing && return nothing
        kind = :exp
        g = R * frac(P(C[one(C)]), scale(cfromQ(C, k), θp))         # dx = ds/(k s)
        tos(u) = u
        sel = θel
    else
        I = cimag(C)
        kr = to_real(ca * inv(I))
        k = kr === nothing ? nothing : kr isa Q ? kr : crational(kr)
        k === nothing && return nothing
        U_ok(f) = all(u -> f(u) == u, values(Uθ))
        if θinv(R, one(C)) == -R && U_ok(u -> θinv(u, one(C)))                # s = cos kx
            kind = :cos
            g = sym_to_s(R * frac(scale(-2 * I, θp), θp^2 - one(P)))
            tos = u -> sym_to_s(u)
            sel = (θel + one1 / θel) * li(inv(two))
        elseif θinv(R, -one(C)) == -R && U_ok(u -> θinv(u, -one(C)))          # s = sin kx
            kind = :sin
            g = sym_to_s(θscale(R * frac(scale(two, θp), θp^2 + one(P)), I))
            tos = u -> sym_to_s(θscale(u, I))
            sel = (θel - one1 / θel) * li(inv(2 * I))
        elseif θscale(R, -one(C)) == R && U_ok(u -> θscale(u, -one(C)))       # s = tan kx
            kind = :tan
            g = tan_to_s(R)
            onep = frac(P(C[one(C), zero(C), one(C)]))
            tos = u -> (v = tan_to_s(u); v === nothing ? nothing : v * onep)
            sel = li(-I) * (θel * θel - one1) / (θel * θel + one1)
        else
            return nothing
        end
        g === nothing && return nothing
        g = g * kconst(inv(cfromQ(C, k)))               # dx = du/k
    end
    Usx = Dict{String,Any}()
    for (kk, u) in Uθ
        v = tos(u)
        v === nothing && return nothing
        Usx[kk] = v
    end
    # exact checks: g(s(θ))·s′ = R and Ũⱼ(s(θ)) = Uⱼ
    gs(p) = foldr((c, acc) -> acc * sel + li(c), p.c; init = zero(sel))
    sub(h) = gs(h.num) / gs(h.den)
    sub(g) * D(T, 1, sel) == liftto(T, el, 1) || throw(RischError("internal check failed: monomial substitution"))
    for (kk, v) in Usx
        sub(v) == liftto(T, Us[kk], 1) || throw(RischError("internal check failed: radicand in the substitution variable"))
    end
    # real coefficients
    RC = cx ? real_ctype(C) : C
    function real_frac(h)
        cx || return h
        n, d = [to_real(c) for c in h.num.c], [to_real(c) for c in h.den.c]
        (any(isnothing, n) || any(isnothing, d)) && return nothing
        frac(UPoly{RC}(RC[n...]), UPoly{RC}(RC[d...]))
    end
    gr = real_frac(g)
    gr === nothing && return nothing
    # the radicals as terms in s (the variable x stands for s), as generators of the constant field
    bd = Builder(build === nothing ? auto_build(f, x) : build, lift === nothing ? auto_lift(f, x) : lift, x, T.consts)
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
    G = frac_term(bs, gr)
    H = risch_integrate(G, x; build = build, lift = lift, verify = verify)
    H isa IntegralWithRootSums && return nothing
    ut = isone(k) ? bd.x : mk(bd, :*, cterm(bd, k), bd.x)
    st = mk(bd, kind, ut)
    back(t) = isnode(t) ? term_rebuild(bd, t, Any[back(s) for s in arguments(t)]) : (string(t) == xk ? st : t)
    back(H)
end

# the order of s in h ∈ C(s): h = sᵐ·(unit at s = 0)
function s_valuation(h::Frac)
    v(p) = (i = findfirst(c -> !iszero(c), p.c); i === nothing ? 0 : i - 1)
    v(h.num) - v(h.den)
end
