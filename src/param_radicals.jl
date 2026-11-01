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

function integrate_param_radicals(f, x, rads; build = nothing, lift = nothing, verify::Bool = true, rational::Bool = false)
    @nospecialize f x
    xk = string(x)
    rational || any(((_, u),) -> has_param(u, xk), rads) || return nothing
    ut0 = rational ? rads[1][2] : first(u for (_, u) in rads if has_param(u, xk))
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
    # the sign of a parameter constant: the oracle's, else at the parameter values of `param_value` (step SO)
    pos(c) = param_sign(c, T.consts) == 1
    if isone(Dn) && degree(N) == 2
        A, B, Cc = co(N, 3), co(N, 2), co(N, 1)
        h = -B / (A + A)
        D = Cc - B * B / (4 * A)
        iszero(D) && return nothing
        # s² = -D/A: D(1 - u²), or (-D)(u² - 1) when D < 0; s² = D/A: D(1 + u²). s from the parameter field,
        # else √(∓D/A) as an opaque constant (`(:sqrt, r)`), the sign positive at the parameter values
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
        # no real values at those parameter values ((e x - 1 - k x²) at e = 1, k = 2): with A < 0 there, the form
        # that has real values for other parameters is D(1 - u²), s = √(-D/A) (D > 0 taken, as Rubi does)
        if sh === nothing && pos(-A)
            s2 = -D / A
            σs = csqrt(s2)
            sh = (σs === nothing ? (:sqrt, s2) : σs, h, D, frac(QX(Q[1, 0, -1])))
        end
    elseif degree(N) == 1 && degree(Dn) == 1           # (n₁x + n₀)/(d₁x + d₀)
        xN, xD = -co(N, 1) / co(N, 2), -co(Dn, 1) / co(Dn, 2)
        # κ u/(u - 1), or (-κ) u/(1 - u) when only -κ is a square, or, neither a square, when κ < 0 at the
        # parameter values ((a³ cos² x + b³ sin² x)/cos² x, a < b: then 0 < u < 1)
        κ0 = co(N, 2) / co(Dn, 2)
        neg = csqrt(κ0) === nothing && (csqrt(-κ0) !== nothing || !pos(κ0))
        sh = neg ?
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
        param_sign(s, T.consts) == -1 && (s = -s)
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
        elseif isone(denominator(k))
            # (√κ as in s = √(D/A), not κ^(1/2): the two would be independent constants of the tower, and
            # x²/((1 + 2x²)√(c + x²)) needed a RootSum)
            kk = Int(numerator(k))
            kk == 1 ? mk(b0, :sqrt, cterm(b0, κ)) : mk(b0, :^, mk(b0, :sqrt, cterm(b0, κ)), b0.lift(kk))
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
    # the factors free of x out (√κ and s, also inside a denominator: x²/((1 + 2x²)√(c + d x²)) gives
    # √c √(1 + u²) there, and with √c inside the integrand the residues needed a RootSum)
    fs = product_factors!(Any[], g, 1)
    pw(t, e) = e == 1 ? t : mk(b0, :^, t, b0.lift(e))
    cf = Any[pw(t, e) for (t, e) in fs if !has_leaf(t, xk)]
    if !isempty(cf) && length(cf) < length(fs)
        rest = Any[pw(t, e) for (t, e) in fs if has_leaf(t, xk)]
        cg = length(cf) == 1 ? cf[1] : mk(b0, :*, cf...)
        g = length(rest) == 1 ? rest[1] : mk(b0, :*, rest...)
    else
        cg = nothing
    end
    G = risch_integrate(g, x; build = b0.build, lift = b0.lift, verify = verify)
    if G isa IntegralWithRootSums                       # a RootSum over ℚ(a, …): scale by a parameter (step PS)
        G = integrate_scaled_radicals(g, x; build = b0.build, lift = b0.lift, verify = verify)
        G === nothing && return nothing
    end
    cg === nothing || (G = G isa IntegralWithRootSums ?
        IntegralWithRootSums(mk(b0, :*, cg, G.elementary), Any[ScaledRootSum(cg, rs) for rs in G.rootsums], G.var) :
        mk(b0, :*, cg, G))
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

# step SO: the caller's sign oracle, the `sign` keyword of `risch_integrate`. Called with a parameter
# expression (a term built like the answer), it returns +1, -1, 0 or nothing (undecided). Every decision
# that depends on the sign of a parameter expression asks it first (`param_sign`, `csign`); undecided
# ones are made at the parameter values of `param_value`, the k-th parameter set to -k when the oracle
# says it is negative, so that the two agree. Without an oracle, the values are 1, 2, … as before.
struct SignOracle
    f::Any
    build::Any
    lift::Any
    x::Any
    cache::Dict{Any,Union{Int,Nothing}}
end
const SIGN_ORACLE = Base.ScopedValues.ScopedValue{Union{Nothing,SignOracle}}(nothing)
# the oracle's 0 for an expression that is not identically 0: a special case of the parameters. Not a
# RischNotImplemented, which other methods catch to try theirs (that do not ask); `risch_integrate` turns
# it into one.
struct SignOracleZero <: Exception
    msg::String
end

function oracle_ask(o::SignOracle, key, t)
    get!(o.cache, key) do
        s = o.f(t)
        s === nothing && return nothing
        s in (-1, 0, 1) || throw(ArgumentError("the sign oracle returned $s for $t: +1, -1, 0 or nothing expected"))
        Int(s)
    end
end
# the oracle's sign of a constant c (not identically 0), or nothing (no oracle, undecided, or c has no term)
function oracle_sign(c, consts)
    o = SIGN_ORACLE[]
    o === nothing && return nothing
    t = try
        cterm(Builder(o.build, o.lift, o.x, consts), c)
    catch err
        (err isa RischNotImplemented || err isa RischError) || rethrow()
        return nothing
    end
    s = oracle_ask(o, (c, consts), t)
    s == 0 && throw(SignOracleZero("the sign oracle says $t = 0: a special case of the parameters"))
    s
end
# the oracle's sign of a term t in the parameters (built like the answer), or nothing (no oracle, undecided)
function term_oracle_sign(t)
    o = SIGN_ORACLE[]
    o === nothing && return nothing
    s = oracle_ask(o, string(t), t)
    s == 0 && throw(SignOracleZero("the sign oracle says $t = 0: a special case of the parameters"))
    s
end
# step SO, log arguments: with an oracle, each c·log(w) of the answer (a summand, w depending on x) becomes
# log(-w) where the oracle says w < 0 (on the caller's domain, assumptions about x included): the same
# derivative, and real there. Undecided, or without an oracle, log(w) stays: on an interval where w < 0 it
# differs from a real antiderivative by the constant iπ·c (the convention of Mathematica). A log inside
# another function is left alone: in log(1 + log x) the inner log is not a summand, and log(-x) would change
# the answer. The term is returned as it is (===) when nothing changes.
function oracle_real_logs(t, bd::Builder, xk::String, o::SignOracle)
    safe_iscall(t) || return t
    n, args = opname(operation(t)), arguments(t)
    sub(a) = oracle_real_logs(a, bd, xk, o)
    function rebuild(f, new)
        all(((a, b),) -> a === b, zip(args, new)) && return t
        f(new...)
    end
    if n === :+
        return rebuild((as...) -> mk(bd, :+, as...), Any[sub(a) for a in args])
    elseif n === :*
        k = findall(a -> depends_on(a, xk), args)
        length(k) == 1 || return t
        return rebuild((as...) -> mk(bd, :*, as...), Any[i == k[1] ? sub(a) : a for (i, a) in enumerate(args)])
    elseif n === :-
        return rebuild((as...) -> bd.build(-, as...), Any[sub(a) for a in args])
    elseif n === :/ && length(args) == 2 && !depends_on(args[2], xk)
        return rebuild((as...) -> mk(bd, :/, as...), Any[sub(args[1]), args[2]])
    elseif n === :log && length(args) == 1 && depends_on(args[1], xk)
        oracle_ask(o, string(args[1]), args[1]) == -1 && return mk(bd, :log, neg_term(bd, args[1]))
    end
    t
end
# -w as a term: the sign taken into a numerator, the terms of a sum or a rational factor
function neg_term(bd::Builder, w)
    if safe_iscall(w)
        n, args = opname(operation(w)), arguments(w)
        n === :/ && length(args) == 2 && return mk(bd, :/, neg_term(bd, args[1]), args[2])
        n === :+ && return mk(bd, :+, Any[neg_term(bd, a) for a in args]...)
        if n === :* && (r = leaf_rational(args[1])) !== nothing
            rest = args[2:end]
            return isone(-r) ? (length(rest) == 1 ? rest[1] : mk(bd, :*, rest...)) : mk(bd, :*, cterm(bd, -Q(r)), rest...)
        end
    elseif (r = leaf_rational(w)) !== nothing
        return cterm(bd, -Q(r))
    end
    mk(bd, :*, bd.lift(-1), w)
end
# the sign of the parameter g itself: -1 when the oracle says g < 0, else +1
function oracle_sym_sign(g::ConstGen)
    o = SIGN_ORACLE[]
    o === nothing && return 1
    s = oracle_ask(o, string(g.term), g.term)
    s == 0 && throw(SignOracleZero("the sign oracle says $(g.term) = 0: a special case of the parameters"))
    s == -1 ? -1 : 1
end

# the value of a parameter constant with the k-th parameter (alphabetically) set to ±k (the sign from the
# oracle), or nothing
function param_value(c, consts)
    syms = sort([g for g in consts if g.kind === :sym]; by = g -> string(g.term))
    names = [string(g.term) for g in syms]
    sgs = [oracle_sym_sign(g) for g in syms]           # (outside the try: the oracle's special case is thrown)
    eb = Builder(expr_build, identity, :x, consts)
    function ev(e)
        if e isa Expr && e.head === :call
            return op_function(e)(map(ev, e.args[2:end])...)
        end
        k = findfirst(==(string(e)), names)            # (before Number: SymEngine's symbols are Numbers)
        k === nothing || return float(sgs[k] * k)
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

# the sign of a constant c: exact when c is rational, else the oracle's, else its sign at `param_value`;
# nothing when undecided
function param_sign(c, consts)
    r = crational(c)
    r === nothing || return Int(sign(r))
    s = oracle_sign(c, consts)
    s === nothing || return s
    v = param_value(c, consts)
    v === nothing ? nothing : Int(sign(v))
end

# step PS: f ∈ ℚ(a, …)(x) homogeneous in x and a parameter a: f(a u)·a = aᵏ g(u) with g ∈ ℚ(u)
# (1/(x³ + a³) = a⁻³/(u³ + 1)). g is integrated over ℚ (real forms with √3, …) and u = x/a put back:
# ∫ f dx = aᵏ G(x/a). Used instead of a RootSum over ℚ(a, …); nothing when f is not of this kind.
function integrate_param_scaled(f, x; build = nothing, lift = nothing, verify::Bool = true)
    @nospecialize f x
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

# an n-th root of c in C = ℚ or ℚ(t₁, …) (c > 0 in ℚ when n is even), or nothing
cnthroot(c::Q, n::Int) = (c > 0 || isodd(n)) ? rat_root(c, n) : nothing
function cnthroot(c::Frac{<:UPoly}, n::Int)
    a = pnthroot(c.num, n)
    a === nothing && return nothing
    b = pnthroot(c.den, n)
    b === nothing ? nothing : frac(a, b)
end
function pnthroot(p::UPoly{B}, n::Int) where {B}
    iszero(p) && return nothing
    l = cnthroot(lc(p), n)
    l === nothing && return nothing
    r = UPoly{B}(B[l])
    for (a, e) in squarefree(p)
        e % n == 0 || return nothing
        r = r * a^(e ÷ n)
    end
    r^n == p ? r : nothing
end

# step BN: f ∈ C(x) (C = ℚ or ℚ(a, …)) with denominator λ xʲ (xⁿ + c)ᵏ, n ≥ 3, whose residues need a RootSum
# (c not ± an n-th power: 1/(x³ - 2), 1/(a x³ - b)). With ρ = |c|^(1/n) (an opaque constant, positive by
# `param_sign`) and x = ρ u, xⁿ + c = |c| (uⁿ ± 1); the numerator N(ρu) = Σ Nᵢ ρⁱ uⁱ, and
# ρ^(i+1-j) = |c|^q ρ^m (i + 1 - j = qn + m), so by linearity
#   ∫ f dx = Σᵢ Nᵢ |c|^(q-k)/λ · ρ^m ∫ uⁱ⁻ʲ/(uⁿ ± 1)ᵏ du,
# each integral over ℚ (real forms with √3, √2, …); then u = x/ρ. Nothing when one of them needs a RootSum.
function integrate_binomial_scaled(f, x; build = nothing, lift = nothing, verify::Bool = true)
    @nospecialize f x
    xk = string(x)
    T, el = try
        build_tower(f, xk)
    catch err
        (err isa RischNotImplemented || err isa RischError) || rethrow()
        return nothing
    end
    C = ctype(T)
    (isempty(T.levels) && (C === Q || real_param_field(C))) || return nothing
    Dn = el.den
    j = findfirst(!iszero, Dn.c) - 1                   # Dn = xʲ R, R(0) ≠ 0
    R = UPoly{C}(Dn.c[(j + 1):end])
    sf = squarefree(R)
    (length(sf) == 1 && degree(sf[1][1]) >= 3) || return nothing
    Qf, k = sf[1]
    n = degree(Qf)
    all(iszero, Qf.c[2:n]) || return nothing           # Qf = xⁿ + c
    c = Qf.c[1]
    pos(c) = param_sign(c, T.consts) == 1
    σ = pos(c) ? 1 : -1
    iseven(n) && σ == -1 && !pos(-c) && return nothing  # (no sign at the parameter values)
    r = cfromQ(C, Q(σ)) * c                            # |c|, ρⁿ = r
    isone(r) && return nothing                         # (already uⁿ ± 1)
    lcD = lc(Dn)
    bd = Builder(build === nothing ? auto_build(f, x) : build, lift === nothing ? auto_lift(f, x) : lift, x, T.consts)
    # ρ itself when |c| is an n-th power in C (a³: ρ = a, positive at the parameter values), else |c|^(m/n)
    ρ = cnthroot(r, n)
    ρ !== nothing && !pos(ρ) && (ρ = -ρ)
    ρpow(m) = ρ === nothing ? mk(bd, :^, cterm(bd, r), bd.lift(Q(m) // n)) : cterm(bd, ρ^m)
    Q0 = QX([i == 0 ? Q(σ) : i == n ? Q(1) : Q(0) for i in 0:n])^k
    terms = Any[]
    for (i, Ni) in enumerate(el.num.c)
        i -= 1
        iszero(Ni) && continue
        q, m = fldmod(i + 1 - j, n)
        coef = Ni * r^(q - k) / lcD
        num, den = i >= j ? (QX([l == i - j ? Q(1) : Q(0) for l in 0:(i - j)]), Q0) :
                            (one(QX), QX([l == j - i ? Q(1) : Q(0) for l in 0:(j - i)]) * Q0)
        G = risch_integrate(frac_term(bd, frac(num, den)), x; build = build, lift = lift, verify = verify)
        G isa IntegralWithRootSums && return nothing
        push!(terms, m == 0 ? mk(bd, :*, cterm(bd, coef), G) : mk(bd, :*, cterm(bd, coef), ρpow(m), G))
    end
    isempty(terms) && return bd.lift(0)
    tot = length(terms) == 1 ? terms[1] : mk(bd, :+, terms...)
    back = mk(bd, :/, bd.x, ρpow(1))
    bk(t) = isnode(t) ? term_rebuild(bd, t, Any[bk(a) for a in arguments(t)]) : (string(t) == xk ? back : t)
    bk(tot)
end

# step PS for radicals: x = p u with p a parameter, a radicand homogeneous in (x, p), U(p u) = p^m U₀(u) with U₀
# free of p, written p^(me) U₀^e (p > 0; p^(me) an opaque constant when me ∉ ℤ): ∫ g(x) dx = ∫ g(p u) p du,
# then u = x/p. Nothing when no parameter gives an answer without a RootSum.
function integrate_scaled_radicals(g, x; build = nothing, lift = nothing, verify::Bool = true)
    @nospecialize g x
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
    @nospecialize f x
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
    pos(c) = param_sign(c, T.consts) == 1
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

# ---------------------------------------------------------------------------
# Step PM: a radicand with parameters and repeated factors (multiplicities), u = c sⁿ W/V (s ∈ K(x);
# W, V ∈ K[x] keep the multiplicities mod n; K the parameter field), its radicals of even index n.
# Y = u^(1/n)/s satisfies Yⁿ = w = c W/V, and on the real line Y = ±w^(1/n), the sign σ = Y/w^(1/n)
# locally constant. With F± the integrals of f where u^(k/n) is (±s w^(1/n))ᵏ,
#   ∫ f = (F₊ + F₋)/2 + σ (F₊ - F₋)/2,
# and F₋ = ±F₊ when u occurs once (an odd or even power). For w = c constant (√((a + bx)²) = (a + bx)·σ)
# w^(1/n) = ρ ∈ K is needed (c = ρⁿ); s is taken as ρ s, and σ = u^(1/n)/s multiplies F₊, as Rubi writes it.
# ---------------------------------------------------------------------------

function integrate_param_repeated(f, x, rads; build = nothing, lift = nothing, verify::Bool = true)
    @nospecialize f x
    xk = string(x)
    for us in unique(string(u) for (_, u) in rads if has_param(u, xk))
        ut = first(u for (_, u) in rads if string(u) == us)
        n = lcm([Int(denominator(e)) for (e, u) in rads if string(u) == us])
        iseven(n) || continue
        T, el = try
            build_tower(ut, xk)
        catch err
            (err isa RischNotImplemented || err isa RischError) || rethrow()
            continue
        end
        isempty(T.levels) || continue
        C = ctype(T)
        P = UPoly{C}
        function split_n(p)                             # p/lc(p) = Sⁿ W
            S, W = one(P), one(P)
            for (a, m) in squarefree(p)
                S *= a^(m ÷ n)
                W *= a^(m % n)
            end
            S, W
        end
        SN, WN = split_n(el.num)
        SD, WD = split_n(el.den)
        degree(SN) + degree(SD) > 0 || continue
        c = lc(el.num) / lc(el.den)
        s = frac(SN, SD)
        b0 = Builder(build === nothing ? auto_build(f, x) : build, lift === nothing ? auto_lift(f, x) : lift, x, T.consts)
        wconst = degree(WN) == 0 && degree(WD) == 0
        local wroot                                     # w^(1/n) as a term
        if wconst
            ρ = c
            k = n
            while k > 1 && ρ !== nothing                 # ρⁿ = c, n a power of 2
                iseven(k) || (ρ = nothing; break)
                ρ = csqrt(ρ)
                k ÷= 2
            end
            ρ === nothing && continue
            param_sign(ρ, T.consts) == -1 && (ρ = -ρ)
            s = frac(scale(ρ, SN), SD)                  # ρ s (a + b x for (a + b x)²), and w^(1/n) = 1
            wroot = b0.lift(1)
        else
            wt = frac_term(b0, frac(scale(c, WN), WD))
            wroot = n == 2 ? mk(b0, :sqrt, wt) : mk(b0, :^, wt, b0.lift(Q(1, n)))
        end
        st = frac_term(b0, s)
        ks = Int[]
        function rewrite(t, sg)
            safe_iscall(t) || return t
            args = arguments(t)
            isempty(args) && return t
            rp = radical_parts(t)
            if rp !== nothing && string(rp[2]) == us
                k = Int(rp[1] * n)
                sg == 1 && push!(ks, k)
                y = wconst ? (sg == 1 ? st : mk(b0, :*, b0.lift(-1), st)) :
                    mk(b0, :*, st, sg == 1 ? wroot : mk(b0, :*, b0.lift(-1), wroot))
                return k == 1 ? y : mk(b0, :^, y, b0.lift(k))
            end
            term_rebuild(b0, t, Any[rewrite(a, sg) for a in args])
        end
        integ(g) = try
            risch_integrate(g, x; build = b0.build, lift = b0.lift, verify = verify)
        catch err
            (err isa RischNotImplemented || err isa NotElementary) || rethrow()
            nothing
        end
        Fp = integ(rewrite(f, 1))
        (Fp === nothing || Fp isa IntegralWithRootSums) && continue
        un = n == 2 ? mk(b0, :sqrt, ut) : mk(b0, :^, ut, b0.lift(Q(1, n)))
        σ = mk(b0, :/, un, wconst ? st : mk(b0, :*, st, wroot))
        length(ks) == 1 && return isodd(ks[1]) ? mk(b0, :*, σ, Fp) : Fp
        Fm = integ(rewrite(f, -1))
        (Fm === nothing || Fm isa IntegralWithRootSums) && continue
        half = b0.lift(Q(1, 2))
        return mk(b0, :+, mk(b0, :*, half, mk(b0, :+, Fp, Fm)),
                  mk(b0, :*, half, σ, mk(b0, :+, Fp, mk(b0, :*, b0.lift(-1), Fm))))
    end
    nothing
end

# ---------------------------------------------------------------------------
# Step LL: radicals of two linear radicands L₁ = a + b x, L₂ = c + d x (with parameters) whose exponents add up to
# an integer in each product, as in (a + bx)^(-3/4) (c + dx)^(-1/4): on the real domain (L₁, L₂ ≥ 0 for an even
# index; real roots for an odd one) the product has one radicand,
#   index 2:  L₁^E₁ L₂^E₂ = (L₁ L₂)^E₁ L₂^(E₂ - E₁)     (a quadratic: step PR, with its asin, acosh forms)
#   else:     L₁^E₁ L₂^E₂ = (L₁/L₂)^E₁ L₂^(E₁ + E₂)    (linear-fractional: step PR)
# Nothing when the radicands are not both linear or some product does not combine.
# ---------------------------------------------------------------------------

function rewrite_two_linear(f, x, rads; build = nothing, lift = nothing)
    @nospecialize f x
    xk = string(x)
    us = unique(string(u) for (_, u) in rads)
    (length(us) == 2 && any(((_, u),) -> has_param(u, xk), rads)) || return nothing
    uts = Any[first(u for (_, u) in rads if string(u) == s) for s in us]
    for ut in uts
        T, el = try
            build_tower(ut, xk)
        catch err
            (err isa RischNotImplemented || err isa RischError) || rethrow()
            return nothing
        end
        (isempty(T.levels) && degree(el.num) == 1 && degree(el.den) == 0) || return nothing
    end
    n = lcm([Int(denominator(e)) for (e, _) in rads])
    b0 = Builder(build === nothing ? auto_build(f, x) : build, lift === nothing ? auto_lift(f, x) : lift, x)
    L1, L2 = uts
    v = n == 2 ? mk(b0, :*, L1, L2) : mk(b0, :/, L1, L2)
    pw(t, e) = iszero(e) ? nothing : isone(e) ? t : mk(b0, :^, t, b0.lift(e))
    ismult(t) = (o = opname(operation(t)); o === :* || o === :/ || radical_parts(t) !== nothing ||
                 (o === :^ && (p = leaf_rational(arguments(t)[2]); p !== nothing && isone(denominator(p)))))
    function rw(t)
        (safe_iscall(t) && !isempty(arguments(t))) || return t
        ismult(t) || return term_rebuild(b0, t, Any[rw(a) for a in arguments(t)])
        E = [Q(0), Q(0)]
        fs = Any[]
        for (s, e) in product_factors!(Any[], t, 1)
            rp = radical_parts(s)
            k = rp === nothing ? nothing : findfirst(==(string(rp[2])), us)
            if k === nothing
                push!(fs, pw(rw(s), e))
            else
                E[k] += rp[1] * e
            end
        end
        if !all(iszero, E)
            isone(denominator(E[1] + E[2])) || throw(RischNotImplemented("radicals of $L1 and $L2 that do not combine"))
            push!(fs, pw(v, E[1]), pw(L2, n == 2 ? E[2] - E[1] : E[1] + E[2]))
        end
        fs = Any[t for t in fs if t !== nothing]
        isempty(fs) ? b0.lift(1) : length(fs) == 1 ? fs[1] : mk(b0, :*, fs...)
    end
    g = try
        rw(f)
    catch err
        err isa RischNotImplemented || rethrow()
        return nothing
    end
    length(unique(string(u) for (_, u) in collect_radicals(g, xk))) == 1 ? g : nothing
end
