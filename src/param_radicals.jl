# ---------------------------------------------------------------------------
# Step PR: radicals whose radicand contains symbolic parameters (a² - x², (x - a)(b - x), (a+x)/(a-x), …).
# An affine substitution x = s·u + h (s, h in the parameter field ℚ(a, b, …)) makes the radicand κ·R(u) with
# κ a parameter constant and R ∈ ℚ(u) free of parameters:
#   quadratic A x² + B x + C: h = -B/(2A), D = C - B²/(4A), s² = ∓D/A (a square in the parameter field):
#     A s²u² + D = D(1 ∓ u²)                        (a² - x² = a²(1 - u²), (x-a)(b-x) = ((b-a)/2)²(1 - u²))
#   (n₁x + n₀)/(d₁x + d₀): the zeros x_N, x_D to 0 and 1: (n₁/d₁)·u/(u - 1)
#   n₁x + n₀: the zero to 0: n₁ s·u
# Then u^e = κ^e R^e (κ = σ² gives σ^(2e)), the integrand f(s u + h)·s is integrated (parameters outside the
# radical are constants of the tower, step SY), and u = (x - h)/s is put back. x itself serves as u. Answers
# hold for the parameter values where σ (or κ) is positive, the usual convention of symbolic integrators.
# ---------------------------------------------------------------------------

function integrate_param_radicals(f, x, rads; build = nothing, lift = nothing, verify::Bool = true)
    xk = string(x)
    any(((_, u),) -> has_param(u, xk), rads) || return nothing
    ut0 = first(u for (_, u) in rads if has_param(u, xk))
    # every radical must have this radicand (or a radicand free of parameters is not mixed in)
    all(((_, u),) -> string(u) == string(ut0), rads) || return nothing
    T, el = try
        build_tower(ut0, xk)
    catch err
        (err isa RischNotImplemented || err isa RischError) || rethrow()
        return nothing
    end
    isempty(T.levels) || return nothing
    C = ctype(T)
    P = UPoly{C}
    N, Dn = el.num, el.den
    kc(c) = frac(P([c]))
    co(p, i) = i <= length(p.c) ? p.c[i] : zero(C)
    sh = nothing                                        # (s, h, κ, R ∈ ℚ(u))
    if isone(Dn) && degree(N) == 2
        A, B, Cc = co(N, 3), co(N, 2), co(N, 1)
        h = -B / (A + A)
        D = Cc - B * B / (4 * A)
        iszero(D) && return nothing
        # s² = -D/A: D(1 - u²), or (-D)(u² - 1) when D < 0; s² = D/A: D(1 + u²). s from the parameter field,
        # else √(∓D/A) as an opaque constant (`(:sqrt, r)`), the sign positive at the parameter values of
        # `param_value` (a = 1, b = 2, …)
        pos(c) = (r = crational(c); r !== nothing ? r > 0 : (v = param_value(c, T.consts); v !== nothing && v > 0))
        function quad_form(sg, s)
            sg == 1 && return (s, h, D, frac(QX(Q[1, 0, 1])))
            pos(D) ? (s, h, D, frac(QX(Q[1, 0, -1]))) : (s, h, -D, frac(QX(Q[-1, 0, 1])))
        end
        for sg in (-1, 1)
            s = csqrt(sg == -1 ? -D / A : D / A)
            s === nothing && continue
            sh = quad_form(sg, s)
            break
        end
        if sh === nothing
            for sg in (-1, 1)
                r = sg == -1 ? -D / A : D / A
                pos(r) || continue
                sg == 1 && !pos(D) && continue          # (D(1 + u²) < 0: no real values)
                sh = quad_form(sg, (:sqrt, r))
                break
            end
        end
    elseif degree(N) == 1 && degree(Dn) == 1           # (n₁x + n₀)/(d₁x + d₀)
        xN, xD = -co(N, 1) / co(N, 2), -co(Dn, 1) / co(Dn, 2)
        κ0 = co(N, 2) / co(Dn, 2)                       # κ u/(u - 1), or (-κ) u/(1 - u) when only -κ is a square
        sh = (csqrt(κ0) === nothing && csqrt(-κ0) !== nothing) ?
             (xD - xN, xN, -κ0, frac(QX(Q[0, 1]), QX(Q[1, -1]))) :
             (xD - xN, xN, κ0, frac(QX(Q[0, 1]), QX(Q[-1, 1])))
    elseif isone(Dn) && degree(N) == 1                  # n₁x + n₀ = u with s = 1/n₁: κ = 1
        sh = (inv(co(N, 2)), -co(N, 1) / co(N, 2), one(C), frac(QX(Q[0, 1])))
    end
    sh === nothing && return nothing
    s, h, κ, Ru = sh
    # orientation: s > 0 when the parameters increase in alphabetical order (a < b, as such problems are
    # written); s and -s both give antiderivatives where the radicand is positive, but they differ across
    # the branch cuts elsewhere
    # (the quadratic case only: R(u) = 1 ± u² is even, so u ↦ -u keeps it)
    if isone(Dn) && degree(N) == 2 && !(s isa Tuple)
        sv = param_value(s, T.consts)
        (sv !== nothing && sv < 0) && (s = -s)
    end
    b0 = Builder(build === nothing ? auto_build(f, x) : build, lift === nothing ? auto_lift(f, x) : lift, x, T.consts)
    st, ht = s isa Tuple ? mk(b0, :sqrt, cterm(b0, s[2])) : cterm(b0, s), cterm(b0, h)
    σ = csqrt(κ)                                        # (else √κ is an opaque constant of the parameters)
    Rt = frac_term(b0, Ru)
    function radval(e)                                  # κ^e R(x)^e as a term
        k = 2 * e
        # κ^(k/2) = |σ|^k: for odd k, |σ| = √(σ²) (the sign of σ depends on the order of the parameters)
        κe = if σ !== nothing && isone(denominator(k))
            kk = Int(numerator(k))
            sr = crational(σ)
            aσ = sr !== nothing ? cterm(b0, abs(sr)) : iseven(kk) ? cterm(b0, σ) :
                 mk(b0, :sqrt, mk(b0, :^, cterm(b0, σ), b0.lift(2)))
            kk == 1 ? aσ : mk(b0, :^, aσ, b0.lift(kk))
        else
            mk(b0, :^, cterm(b0, κ), b0.lift(e))
        end
        Re = isone(e * 2) ? mk(b0, :sqrt, Rt) : mk(b0, :^, Rt, b0.lift(e))
        isone(κ) ? Re : mk(b0, :*, κe, Re)              # (κ = 1: no factor 1^e)
    end
    sone = !(s isa Tuple) && isone(s)
    sx = sone ? b0.x : mk(b0, :*, st, b0.x)
    xnew = iszero(h) ? sx : mk(b0, :+, sx, ht)
    function walk(t)
        safe_iscall(t) || return string(t) == xk ? xnew : t
        args = arguments(t)
        isempty(args) && return t
        rp = radical_parts(t)
        (rp !== nothing && string(rp[2]) == string(ut0)) && return radval(rp[1])
        b0.build(op_function(t), (walk(a) for a in args)...)
    end
    g = mk(b0, :*, walk(f), st)                         # f(s x + h) · s
    G = risch_integrate(g, x; build = b0.build, lift = b0.lift, verify = verify)
    if G isa IntegralWithRootSums                       # a RootSum over ℚ(a, …): scale by a parameter (step PS)
        G = integrate_scaled_radicals(g, x; build = b0.build, lift = b0.lift, verify = verify)
        G === nothing && return nothing
    end
    xh = iszero(h) ? b0.x : mk(b0, :+, b0.x, mk(b0, :*, b0.lift(-1), ht))
    back = sone ? xh : mk(b0, :/, xh, st)               # x ↦ (x - h)/s
    function walk_back(t)
        safe_iscall(t) || return string(t) == xk ? back : t
        args = arguments(t)
        isempty(args) && return t
        b0.build(op_function(t), (walk_back(a) for a in args)...)
    end
    walk_back(G)
end

# a symbol other than the integration variable (a parameter) in t
has_param(t, xk::String) = safe_iscall(t) && !isempty(arguments(t)) ? any(a -> has_param(a, xk), arguments(t)) :
                           (string(t) != xk && leaf_rational(t) === nothing && !is_e_const(t) && !(string(t) in ("pi", "π")))

# the value of a parameter constant with the k-th parameter (alphabetically) set to k, or nothing
function param_value(c, consts)
    names = sort([string(g.term) for g in consts if g.kind === :sym])
    eb = Builder((op, args...) -> Expr(:call, nameof(op), args...), identity, :x, consts)
    function ev(e)
        if e isa Expr && e.head === :call
            return op_function(e)(map(ev, e.args[2:end])...)
        end
        k = findfirst(==(string(e)), names)            # (before Number: SymEngine's symbols are Numbers)
        k === nothing || return float(k)
        r = leaf_rational(e)
        r === nothing && throw(RischError("no value for $e"))
        float(r)
    end
    try
        v = ev(cterm(eb, c))
        v isa Real && isfinite(v) ? v : nothing
    catch
        nothing
    end
end

# step PS: f ∈ ℚ(a, …)(x) homogeneous in x and a parameter a: f(a u)·a = aᵏ g(u) with g ∈ ℚ(u)
# (1/(x³ + a³) = a⁻³/(u³ + 1)). g is integrated over ℚ (real forms with √3, …) and u = x/a put back:
# ∫ f dx = aᵏ G(x/a). Used instead of a RootSum over ℚ(a, …); nothing when f is not of this kind.
function integrate_param_scaled(f, x; build = nothing, lift = nothing, verify::Bool = true)
    xk = string(x)
    T, el = try
        build_tower(f, xk)
    catch err
        (err isa RischNotImplemented || err isa RischError) || rethrow()
        return nothing
    end
    (isempty(T.levels) && real_param_field(ctype(T))) || return nothing
    C = ctype(T)
    for j in eachindex(T.consts)
        T.consts[j].kind === :sym || continue
        # the coefficients cᵢ aʲ… of N(a u): each must be r·a^m with one m for all of them
        function scaled(p)
            m, qs = nothing, Q[]
            for (i, c) in enumerate(p.c)
                if iszero(c)
                    push!(qs, Q(0))
                    continue
                end
                mono = const_monomial(c)
                mono === nothing && return nothing
                r, ks = mono
                all(((jj, _),) -> jj == j, ks) || return nothing
                e = (isempty(ks) ? 0 : ks[1][2]) + (i - 1)
                m === nothing ? (m = e) : (m == e || return nothing)
                push!(qs, r)
            end
            m, QX(qs)
        end
        sn, sd = scaled(el.num), scaled(el.den)
        (sn === nothing || sd === nothing) && continue
        k = sn[1] - sd[1] + 1
        b0 = Builder(build === nothing ? auto_build(f, x) : build, lift === nothing ? auto_lift(f, x) : lift, x, T.consts)
        G = risch_integrate(frac_term(b0, frac(sn[2], sd[2])), x; build = b0.build, lift = b0.lift, verify = verify)
        G isa IntegralWithRootSums && return nothing
        at = T.consts[j].term
        back = mk(b0, :/, b0.x, at)                     # u = x/a
        function walk_back(t)
            safe_iscall(t) || return string(t) == xk ? back : t
            args = arguments(t)
            isempty(args) && return t
            b0.build(op_function(t), (walk_back(a) for a in args)...)
        end
        Gx = walk_back(G)
        return iszero(k) ? Gx : mk(b0, :*, isone(k) ? at : mk(b0, :^, at, b0.lift(k)), Gx)
    end
    nothing
end

# step PS for radicals: x = p u with p a parameter, a radicand homogeneous in (x, p), U(p u) = p^m U₀(u) with U₀
# free of p, written p^(me) U₀^e (p > 0; p^(me) an opaque constant when me ∉ ℤ): ∫ g(x) dx = ∫ g(p u) p du,
# then u = x/p. Nothing when no parameter gives an answer without a RootSum.
function integrate_scaled_radicals(g, x; build = nothing, lift = nothing, verify::Bool = true)
    xk = string(x)
    bd = Builder(build === nothing ? auto_build(g, x) : build, lift === nothing ? auto_lift(g, x) : lift, x)
    ps = Dict{String,Any}()
    collect_params(t) = isnode(t) ? foreach(collect_params, arguments(t)) :
                        (has_param(t, xk) && (ps[string(t)] = t))
    collect_params(g)
    for (pk, p) in ps
        px = mk(bd, :*, p, bd.x)
        sx(t) = isnode(t) ? term_rebuild(bd, t, Any[sx(a) for a in arguments(t)]) : (string(t) == xk ? px : t)
        ok = Ref(true)
        function rw(t)
            isnode(t) || return string(t) == xk ? px : t
            rp = radical_parts(t)
            if rp !== nothing && depends_on(rp[2], xk)
                e, u = rp
                T, el = try
                    build_tower(sx(u), xk)
                catch err
                    (err isa RischNotImplemented || err isa RischError) || rethrow()
                    ok[] = false
                    return t
                end
                j = findfirst(c -> c.kind === :sym && string(c.term) == pk, T.consts)
                if !isempty(T.levels) || j === nothing
                    ok[] = false
                    return t
                end
                hn, hd = hom_in(el.num, j), hom_in(el.den, j)
                if hn === nothing || hd === nothing
                    ok[] = false
                    return t
                end
                me = (hn[1] - hd[1]) * e
                U0 = frac_term(bd, frac(hn[2], hd[2]))
                r0 = isone(e * 2) ? mk(bd, :sqrt, U0) : mk(bd, :^, U0, bd.lift(e))
                iszero(me) && return r0
                return mk(bd, :*, isone(me) ? p : mk(bd, :^, p, bd.lift(me)), r0)
            end
            term_rebuild(bd, t, Any[rw(a) for a in arguments(t)])
        end
        h = mk(bd, :*, rw(g), p)
        ok[] || continue
        # radical-free subterms homogeneous in p: p^k times a rational term free of p (a x + a = a (x + 1))
        function norm(t)
            isnode(t) || return t
            if depends_on(t, xk) && has_param(t, xk) && isempty(collect_radicals(t, xk))
                T, el = try
                    build_tower(t, xk)
                catch err
                    (err isa RischNotImplemented || err isa RischError) || rethrow()
                    (nothing, nothing)
                end
                if T !== nothing && isempty(T.levels)
                    j = findfirst(c -> c.kind === :sym && string(c.term) == pk, T.consts)
                    hn, hd = j === nothing ? (nothing, nothing) : (hom_in(el.num, j), hom_in(el.den, j))
                    if hn !== nothing && hd !== nothing
                        k = hn[1] - hd[1]
                        r = frac_term(bd, frac(hn[2], hd[2]))
                        return iszero(k) ? r : mk(bd, :*, isone(k) ? p : mk(bd, :^, p, bd.lift(k)), r)
                    end
                end
            end
            term_rebuild(bd, t, Any[norm(a) for a in arguments(t)])
        end
        h = norm(h)
        # the factors of the product, those free of x in front (step IT takes them out of the integral)
        facs = Any[]
        flat(t) = (isnode(t) && opname(operation(t)) === :*) ? foreach(flat, arguments(t)) : push!(facs, t)
        flat(h)
        cf, xf = [t for t in facs if !depends_on(t, xk)], [t for t in facs if depends_on(t, xk)]
        prod_t(l) = isempty(l) ? bd.lift(1) : length(l) == 1 ? l[1] : mk(bd, :*, l...)
        h = isempty(cf) ? prod_t(xf) : mk(bd, :*, prod_t(cf), prod_t(xf))
        H = try
            risch_integrate(h, x; build = build, lift = lift, verify = verify)
        catch err
            (err isa RischNotImplemented || err isa NotElementary) || rethrow()
            continue
        end
        H isa IntegralWithRootSums && continue
        back(t) = isnode(t) ? term_rebuild(bd, t, Any[back(a) for a in arguments(t)]) :
                  (string(t) == xk ? mk(bd, :/, bd.x, p) : t)
        return back(H)
    end
    nothing
end

# the coefficients of q as r_i p^m with one m (p the j-th generator): (m, ∑ r_i xⁱ), else nothing
function hom_in(q, j::Int)
    m, qs = nothing, Q[]
    for c in q.c
        iszero(c) && (push!(qs, Q(0)); continue)
        mono = const_monomial(c)
        mono === nothing && return nothing
        r, ks = mono
        all(((jj, _),) -> jj == j, ks) || return nothing
        mm = isempty(ks) ? 0 : ks[1][2]
        m === nothing ? (m = mm) : (m == mm || return nothing)
        push!(qs, r)
    end
    (m === nothing ? 0 : m), QX(qs)
end

# ---------------------------------------------------------------------------
# Step PL: rational functions over a parameter field whose denominator is a power of one quadratic (or
# linear) polynomial with parameters, (b₁ + c₁x)/(a + 2bx + cx²)⁴: Hermite reduction over ℚ(a, b, c, b₁, c₁)
# swells (×10 per power). With x = s u + h (as in step PR), Q(su + h) = κ Q₀(u), Q₀ ∈ ℚ[u]; the numerator is
# Σ nᵢ sⁱ uⁱ with nᵢ constants, sⁱ = r^⌊i/2⌋ s^(i mod 2) (s² = r ∈ the field; s itself may be an opaque
# √r). By linearity ∫ f dx = s κ⁻ᵏ Σ nᵢ sⁱ ∫ uⁱ/Q₀(u)ᵏ du, each integral over ℚ; then u = (x - h)/s.
# ---------------------------------------------------------------------------
function integrate_param_linear(f, x; build = nothing, lift = nothing, verify::Bool = true)
    xk = string(x)
    T, el = try
        build_tower(f, xk)
    catch err
        (err isa RischNotImplemented || err isa RischError) || rethrow()
        return nothing
    end
    (isempty(T.levels) && real_param_field(ctype(T))) || return nothing
    C = ctype(T)
    Dn = el.den
    sf = squarefree(Dn)
    (length(sf) == 1 && sf[1][2] >= 2) || return nothing
    Qf, k = sf[1]
    lcD = lc(Dn)                                       # Dn = lcD Qf^k (Qf monic)
    co(p, i) = i <= length(p.c) ? p.c[i] : zero(C)
    pos(c) = (r = crational(c); r !== nothing ? r > 0 : (v = param_value(c, T.consts); v !== nothing && v > 0))
    if degree(Qf) == 1                                  # Qf = x - x₀: u = x - x₀, Q₀ = u
        s, r, h, κ, Q0 = one(C), one(C), -co(Qf, 1), one(C), QX(Q[0, 1])
    elseif degree(Qf) == 2
        B, Cc = co(Qf, 2), co(Qf, 1)                    # x² + Bx + Cc = (x + B/2)² + D
        h = -B * cfromQ(C, Q(1, 2))
        D = Cc - B * B * cfromQ(C, Q(1, 4))
        iszero(D) && return nothing
        sgn = pos(D) ? 1 : -1                           # D (u² + 1) or -D (u² - 1) with s² = |D|
        r = cfromQ(C, Q(sgn)) * D
        s = csqrt(r)
        s === nothing && (s = (:sqrt, r))
        κ, Q0 = r, QX(Q[sgn, 0, 1])
    else
        return nothing
    end
    bd = Builder(build === nothing ? auto_build(f, x) : build, lift === nothing ? auto_lift(f, x) : lift, x, T.consts)
    st = s isa Tuple ? mk(bd, :sqrt, cterm(bd, s[2])) : cterm(bd, s)
    # numerator N(s u + h) = Σᵢ nᵢ sⁱ uⁱ: Taylor coefficients at h
    N = el.num
    terms = Any[]                                       # s^(i+1): r^((i+1)/2) for odd i, r^(i/2) s for even i
    for i in 0:degree(N)
        # nᵢ = N⁽ⁱ⁾(h)/i!
        Ni = N
        for _ in 1:i
            Ni = deriv(Ni)
        end
        ni = foldr((c, acc) -> acc * h + c, Ni.c; init = zero(C)) / cfromQ(C, Q(factorial(big(i))))
        iszero(ni) && continue
        coef = ni * r^(i ÷ 2) / (lcD * κ^k)             # × s^(i mod 2) × s (dx = s du)
        coef = isodd(i) ? coef * r : coef
        G = risch_integrate(frac_term(bd, frac(QX([j == i ? Q(1) : Q(0) for j in 0:i]), Q0^k)), x;
                            build = build, lift = lift, verify = verify)
        G isa IntegralWithRootSums && return nothing
        ct = cterm(bd, coef)
        push!(terms, isodd(i) ? mk(bd, :*, ct, G) : mk(bd, :*, ct, st, G))
    end
    isempty(terms) && return bd.lift(0)
    tot = length(terms) == 1 ? terms[1] : mk(bd, :+, terms...)
    xh = iszero(h) ? bd.x : mk(bd, :+, bd.x, cterm(bd, -h))
    back = (s isa Tuple || !isone(s)) ? mk(bd, :/, xh, st) : xh
    bk(t) = isnode(t) ? term_rebuild(bd, t, Any[bk(a) for a in arguments(t)]) : (string(t) == xk ? back : t)
    bk(tot)
end
