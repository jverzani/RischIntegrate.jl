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
        for sg in (-1, 1)                               # s² = -D/A: D(1 - u²); s² = D/A: D(1 + u²)
            s = csqrt(sg == -1 ? -D / A : D / A)
            s === nothing && continue
            sh = (s, h, D, frac(QX(Q[1, 0, sg == -1 ? -1 : 1])))
            break
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
    if isone(Dn) && degree(N) == 2
        sv = param_value(s, T.consts)
        (sv !== nothing && sv < 0) && (s = -s)
    end
    b0 = Builder(build === nothing ? auto_build(f, x) : build, lift === nothing ? auto_lift(f, x) : lift, x, T.consts)
    st, ht = cterm(b0, s), cterm(b0, h)
    σ = csqrt(κ)
    σ === nothing && !isone(κ) && crational(κ) === nothing && return nothing   # √κ would be a radical of the parameters
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
        mk(b0, :*, κe, Re)
    end
    sx = isone(s) ? b0.x : mk(b0, :*, st, b0.x)
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
    G isa IntegralWithRootSums && return nothing
    xh = iszero(h) ? b0.x : mk(b0, :+, b0.x, mk(b0, :*, b0.lift(-1), ht))
    back = isone(s) ? xh : mk(b0, :/, xh, st)           # x ↦ (x - h)/s
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
