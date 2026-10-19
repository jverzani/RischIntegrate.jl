# ---------------------------------------------------------------------------
# Step 10a: radicals of one linear-fractional radicand, by substitution
#
# All radicals u^(p/q) (sqrt, cbrt, ^ with a non-integer rational exponent) must share one
# radicand u = (a x + b)/(c x + d) ∈ ℚ(x) with ad - bc ≠ 0. With n = lcm of the q's and
# t = u^(1/n):  x = φ(t) = (b - d tⁿ)/(c tⁿ - a),  u^(p/q) = t^(pn/q),  dx = φ'(t) dt.
# The integrand is parsed straight into a tower over ℚ(t) (parse hook `T.subst`), multiplied
# by φ'(t), integrated and verified exactly there; the answer is printed with the base
# variable t written as the term u^(1/n) (sqrt(u) for n = 2), i.e. as a function of x.
# Anything else with radicals (several radicands, radicands of degree ≥ 2, nested radicals)
# raises RischNotImplemented. Principal roots: answers are valid where u > 0.
# ---------------------------------------------------------------------------

# (exponent, radicand term) when t is u^e with e ∈ ℚ \ ℤ (sqrt, cbrt, ^), else nothing
function radical_parts(t)
    safe_iscall(t) || return nothing
    args = arguments(t)
    isempty(args) && return nothing
    n = opname(operation(t))
    n === :sqrt && length(args) == 1 && return (Q(1) // 2, args[1])
    n === :cbrt && length(args) == 1 && return (Q(1) // 3, args[1])
    if n === :^ && length(args) == 2 && !is_e_const(args[1])
        e = leaf_rational(args[2])
        (e !== nothing && !isone(denominator(e))) && return (Q(e), args[1])
    end
    nothing
end

# all radicals of f: [(exponent, radicand term)]
function collect_radicals(f, xk::String, out = Tuple{Q,Any}[])
    rp = radical_parts(f)
    rp === nothing || push!(out, rp)
    if safe_iscall(f)
        for a in arguments(f)
            collect_radicals(a, xk, out)
        end
    end
    out
end

# the radicand as an element of ℚ(x), or nothing
function radicand_element(u, xk::String)
    T, el = try
        build_tower(u, xk)
    catch e
        (e isa RischNotImplemented || e isa RischError) && return nothing
        rethrow()
    end
    (isempty(T.levels) && ctype(T) === Q) ? el : nothing
end

# φ ∈ S(t) (same representation as S(x); S = ℚ or the tower's constant field) as an element
# of K_0 of the tower T
to_K0(T::Tower, φ::Frac{UPoly{Q}}) = (C = ctype(T); P = UPoly{C};
    frac(P(C[cfromQ(C, c) for c in φ.num.c]), P(C[cfromQ(C, c) for c in φ.den.c])))
to_K0(T::Tower{C}, φ::Frac{UPoly{C}}) where {C} = φ

function integrate_radical(f, x, rads; build = nothing, lift = nothing, verify::Bool = true)
    xk = string(x)
    groups = Any[]                                      # [radicand element, term, lcm of indices]
    cvs = Q[]                                           # radicands of constant radicals (10e)
    b0 = Builder(build === nothing ? auto_build(f, x) : build,
                 lift === nothing ? auto_lift(f, x) : lift, x)
    pmap = Dict{Frac{UPoly{Q}},Tuple{Frac{UPoly{Q}},Int}}()   # radicand u ↦ (w, m), u^e = w^(e m) (RP)
    for (e, ut) in rads
        ue = radicand_element(ut, xk)
        ue === nothing && throw(RischNotImplemented(
            "radical of a non-rational expression ($ut): only radicals of rational functions of x are supported"))
        if is_const_radicand(ue)
            denominator(e) == 2 || throw(RischNotImplemented(
                "the constant radical $ut: only square roots of rational constants are supported"))
            push!(cvs, const_radicand(ue))
            continue
        end
        w, m = radicand_power(ue)
        m > 1 && (pmap[ue] = (w, m))
        i = findfirst(g -> g[1] == w, groups)
        i === nothing && (push!(groups, Any[w, m > 1 ? frac_term(b0, w) : ut, 1]); i = length(groups))
        groups[i][3] = lcm(groups[i][3], Int(denominator(e * m)))
    end
    cfix = const_radical_field(cvs)
    if isempty(groups)                                  # only constant radicals: x = t
        tt = frac(xpoly(Q))
        return try_substitutions(f, xk, Any[(Q, tt, (ue, e) -> throw(RischError("unexpected radicand")), x)],
                                 b0, verify, cfix)
    end
    if length(groups) == 2
        linear(g) = isone(g[1].den) && degree(g[1].num) == 1
        # two square roots, not both of linear polynomials: the biquadratic splitting (step BQ)
        (all(g -> g[3] == 2, groups) && !all(linear, groups) && cfix === nothing) &&
            return integrate_biquadratic(f, x, xk, groups, b0, verify, pmap)
        return integrate_two_radicals(f, xk, groups, b0, verify, cfix, pmap)
    end
    length(groups) > 2 && throw(RischNotImplemented(
        "radicals of more than two different radicands (a curve of genus ≥ 1 in general)"))
    u, uterm, n = groups[1]
    N, Dd = u.num, u.den
    co(p, i) = i <= length(p.c) ? p.c[i] : Q(0)
    P = UPoly{Q}
    tt = frac(xpoly(Q))                                 # t ∈ ℚ(t)
    kq(c) = frac(P(Q[c]))
    # step SQ: square roots of a polynomial with repeated factors, u = s² w (w squarefree): the variable
    # is Y = √u/s (Y² = w on every interval, whatever the sign of s), u^(k/2) = sᵏ Yᵏ, and the answer is
    # printed with √u/s for √w
    uo, sq, Yterm = u, nothing, nothing
    if n == 2 && isone(Dd) && isempty(pmap) && degree(N) >= 2
        sf = squarefree(N)
        w = scale(lc(N), prod((p for (p, m) in sf if isodd(m)); init = one(P)))
        if any(((_, m),) -> m >= 2, sf)
            sp = prod((p^(m ÷ 2) for (p, m) in sf); init = one(P))
            degree(w) == 0 && cfix === nothing &&
                return integrate_const_times_square(f, xk, uo, uterm, sp, w, b0, verify)
            degree(w) == 0 && return integrate_square_branches(f, x, xk, uo, uterm, sp, w, b0, verify)
            sq = sp
            u, N = frac(w), w
            Yterm = mk(b0, :/, mk(b0, :sqrt, uterm), poly_term(b0, sp))
        end
    end
    # step SQ for an index n ≥ 3: u = sⁿ (x - a)ʲ (x - b)ᵏ (j + k ≡ 0 mod n, or a single linear factor):
    # u^(1/n) = s (x - b)^((j+k)/n) v^(j/n), v = (x - a)/(x - b) linear-fractional (genus 0, step 10a)
    if n >= 3 && isone(Dd) && isempty(pmap) && degree(N) >= 2 && cfix === nothing
        r = integrate_root_repeated(f, xk, u, uterm, n, b0, verify)
        r === nothing || return r
    end
    # u^e = sᵏ·radpow(k) (k = 2e) for the original radicand, s evaluated at x = φ(t) over S
    sqval(radpow, φ, ::Type{S}) where {S} = function (ue, e)
        ue == uo || throw(RischError("unexpected radicand"))
        k = 2 * e
        isone(denominator(k)) || throw(RischError("radical exponent not a multiple of 1/2"))
        sφ = sum((φ^(i - 1) * frac(UPoly{S}(S[cfromQ(S, c)])) for (i, c) in enumerate(sq.c)); init = zero(φ))
        sφ^Int(numerator(k)) * radpow(Int(numerator(k)))
    end
    if n == 1                                           # every radical is a power of w (RP): x = t
        cands = Any[(Q, tt, k -> u^k, b0.x)]
    elseif degree(N) <= 1 && degree(Dd) <= 1 && degree(N) + degree(Dd) >= 1
        # 10a: u = (a x + b)/(c x + d), t = u^(1/n), x = (b - d tⁿ)/(c tⁿ - a), u^(p/q) = t^(pn/q)
        a, b, c, d = co(N, 2), co(N, 1), co(Dd, 2), co(Dd, 1)
        iszero(a * d - b * c) && throw(RischError("radicand is constant"))
        tn = tt^n
        φ = (kq(b) - kq(d) * tn) / (kq(c) * tn - kq(a))
        tterm = sq !== nothing ? Yterm : n == 2 ? mk(b0, :sqrt, uterm) : mk(b0, :^, uterm, b0.lift(Q(1) // n))
        cands = Any[(Q, φ, k -> tt^k, tterm, sq === nothing ? Any[tt] : Any[])]   # u^(k/n) = t^k; real points: t > 0 (RL)
    elseif isone(Dd) && degree(N) == 2 && n == 2
        # 10b/10c: √Q, Q = A x² + B x + C, by an Euler substitution (rational parametrisation
        # over ℚ, or over ℚ(i)(√d) when the conic R² = Q has no small rational point);
        # Q^(k/2) = ψ(t)^k
        # real points: ψ(t) = √Q > 0 (step EL)
        cands = Any[(S, φ, k -> ψ^k, tterm, sq === nothing ? real_pos(Any[ψ]) : Any[])
                    for (S, φ, ψ, tterm) in euler_substitution(co(N, 3), co(N, 2), co(N, 1), b0, uterm;
                                                               pref = cfix_d(cfix), R = Yterm)]
    elseif isone(Dd) && degree(N) >= 3 && n == 2 && cfix === nothing
        # SI2 phase 1: y² = u of genus ≥ 1, Hermite reduction on the curve (hyperelliptic.jl)
        hradval = function (ue, e)                      # ue^e = yᵏ: k, or (k, sᵏ) for u = s²w (SQ), or nothing
            if sq !== nothing
                ue == uo || return nothing
                k = 2 * e
                return isone(denominator(k)) ? (Int(numerator(k)), frac(sq)^Int(numerator(k))) : nothing
            end
            wm = ue == u ? (u, 1) : get(pmap, ue, nothing)
            (wm === nothing || wm[1] != u) && return nothing
            k = 2 * e * wm[2]
            isone(denominator(k)) ? Int(numerator(k)) : nothing
        end
        return integrate_hyperelliptic(f, xk, u, sq === nothing ? uterm : frac_term(b0, u), hradval, b0, verify;
                                       yterm = Yterm)
    else
        throw(RischNotImplemented(
            "radicals of $uterm: supported are u^(p/q) with u = (ax+b)/(cx+d), and √ of a quadratic " *
            "polynomial; this needs the algebraic Risch algorithm or is not elementary in general"))
    end
    radval(radpow) = function (ue, e)                   # u^e = radpow(e n)
        ue == u || throw(RischError("unexpected radicand"))
        k = e * n
        isone(denominator(k)) || throw(RischError("radical exponent not a multiple of 1/n"))
        radpow(Int(numerator(k)))
    end
    try_substitutions(f, xk, Any[(c[1], c[2], sq === nothing ? radval(c[3]) : sqval(c[3], c[2], c[1]), c[4],
                                  length(c) >= 5 ? c[5] : nothing) for c in cands],
                      b0, verify, cfix, pmap)
end

# Several substitutions (different constant fields, 10c/10d): the first one that is handled
# decides; a NotElementary from any of them is a proof (each is a rational parametrisation).
# With constant radicals (10e, `cfix` = (field, value function)) the tower is built over
# cfix.C; a substitution over another field ℚ(i)(√d') is not combinable (skipped).
function try_substitutions(f, xk::String, cands, b0::Builder, verify::Bool, cfix = nothing, pmap = nothing)
    err = RischNotImplemented("the radicals of x need a constant field other than the one fixed by the constant radicals ($(cfix === nothing ? Q : cfix.C))")
    for c in cands
        S, φ, radval0, tterm = c[1], c[2], c[3], c[4]
        pos = length(c) >= 5 ? c[5] : nothing           # real points of the substitution (RL, EL)
        # u^e = w^(e m) for a radicand that is a power (step RP)
        radval = (pmap === nothing || isempty(pmap)) ? radval0 :
                 (ue, e) -> (wm = get(pmap, ue, nothing); wm === nothing ? radval0(ue, e) : radval0(wm[1], e * wm[2]))
        C = cfix === nothing || cfix.C === Q ? (S === Q ? nothing : S) :
            (S === Q || S === cfix.C) ? cfix.C : continue
        try
            return integrate_subst(f, xk, S, φ, radval, Builder(b0.build, b0.lift, tterm), verify, C, cfix;
                                   pos = pos)
        catch e
            e isa RischNotImplemented || rethrow()
            err = e
        end
    end
    throw(err)
end

# ∫ f dx with x = φ(t) and u^e = radval(u, e) ∈ S(t) for the radicands u ∈ ℚ(x);
# the answer is printed with t as bt.x
function integrate_subst(f, xk::String, ::Type{S}, φ, radval, bt::Builder, verify::Bool,
                         constants = S === Q ? nothing : S, cfix = nothing; pos = nothing) where {S}
    dφ = dx(φ)
    function sub(term, T)
        if !safe_iscall(term)
            return string(term) == xk ? to_K0(T, φ) : nothing
        end
        rp = radical_parts(term)
        rp === nothing && return nothing
        e, ut = rp
        ue = radicand_element(ut, xk)
        ue === nothing && throw(RischNotImplemented("radical of a non-rational expression ($ut)"))
        if is_const_radicand(ue)
            C = ctype(T)
            c = cfix.val(const_radicand(ue), e)
            return frac(UPoly{C}(C[c isa Q ? cfromQ(C, c) : c]))
        end
        to_K0(T, radval(ue, e))
    end
    T, el = build_tower(f, xk; subst = sub, constants = constants)
    T.subst = nothing
    g = el * liftto(T, to_K0(T, dφ), levelof(T, el))     # f(φ(t), …) φ'(t)
    T, g = minimal(T, g)
    bd = Builder(bt.build, bt.lift, bt.x, T.consts)
    integrate_built(T, g, bd, verify; pos = pos)
end

# ---------------------------------------------------------------------------
# Step 10e: square roots of rational constants (sqrt(2), 2^(3/2), sqrt(8), …) as constants
#
# All must lie in one field ℚ(√d) (d the squarefree part of the radicands, d > 0); the tower
# is then built over ℚ(i)(√d) (as in 10c: i for the atan terms, real-form output, sqrt(d)
# symbolic). v^(p/2) = v^((p-1)/2) √v, √v = σ√d. Radicals of x combine with it when their
# substitution is over ℚ or over the same field.
# ---------------------------------------------------------------------------
is_const_radicand(u) = degree(u.num) <= 0 && degree(u.den) <= 0
cfix_d(cfix) = cfix === nothing || cfix.C === Q ? 1 : cfix.C.parameters[1]   # d of ℚ(i)(√d)
const_radicand(u) = isempty(u.num.c) ? Q(0) : u.num.c[1] / u.den.c[1]

# (C, val) with val(v, e) = v^e ∈ C for the constant radicands vs, or nothing if there are none
function const_radical_field(vs)
    isempty(vs) && return nothing
    any(v -> v < 0, vs) && throw(RischNotImplemented(
        "square roots of negative constants (complex constants in the integrand) are not supported"))
    ds = unique([sqfree_split(numerator(v) * denominator(v))[2] for v in vs if !iszero(v)])
    filter!(!isone, ds)
    length(ds) > 1 && throw(RischNotImplemented(
        "square roots of constants with different squarefree parts $(Int.(ds)) (would need ℚ(√d₁, √d₂))"))
    C = isempty(ds) ? Q : QSB{Int(ds[1]),QI}
    function val(v::Q, e::Q)
        iszero(v) && return C === Q ? Q(0) : zero(C)
        p = numerator(2 * e)                            # odd: e = p/2
        r = v^((p - 1) ÷ 2)
        sv = rat_sqrt(v)
        sv !== nothing && return r * sv
        _, s = qs_field(v)
        cfromQ(C, r) * s
    end
    (C = C, val = val)
end

# step SQ, u = c·s² (c constant): Y = √u/s is locally constant, Y² = c. f = f₀ + f₁Y (f₀, f₁ ∈ ℚ(x)), and
# ∫ f = ∫ f₀ + Y ∫ f₁ on each interval where s ≠ 0 (the Euler substitution degenerates on one branch here)
function integrate_const_times_square(f, xk::String, uo, uterm, sp::UPoly{Q}, w::UPoly{Q}, b0::Builder, verify::Bool)
    radval = function (ue, e)
        ue == uo || return nothing
        k = 2 * e
        isone(denominator(k)) ? (Int(numerator(k)), frac(sp)^Int(numerator(k))) : nothing
    end
    el = parse_hyp(f, xk, frac(w), radval)
    T, _ = build_tower(b0.x, xk)
    F0 = iszero(el.p) ? nothing : integrate_built(T, el.p, b0, verify)
    F1 = iszero(el.q) ? nothing : integrate_built(T, el.q, b0, verify)
    (F0 isa IntegralWithRootSums || F1 isa IntegralWithRootSums) && throw(RischNotImplemented(
        "√($uterm): RootSums times a locally constant square root"))
    Y = mk(b0, :/, mk(b0, :sqrt, uterm), poly_term(b0, sp))
    T1 = F1 === nothing ? nothing : mk(b0, :*, Y, F1)
    F0 === nothing ? (T1 === nothing ? b0.lift(0) : T1) : T1 === nothing ? F0 : mk(b0, :+, F0, T1)
end

# step SQ, u = c·s² with other (constant) radicals: on each branch √u = ±s√c, so with F± = ∫ f|_{√u = ±s√c},
# ∫ f = (F₊ + F₋)/2 + σ (F₊ - F₋)/2, σ = sign(s) = (√u/s)/√c (locally constant)
function integrate_square_branches(f, x, xk::String, uo, uterm, sp::UPoly{Q}, w::UPoly{Q}, b0::Builder, verify::Bool)
    c = w.c[1]
    rc = rat_sqrt(c)
    sqc = rc === nothing ? mk(b0, :sqrt, cterm(b0, c)) : cterm(b0, rc)
    st = poly_term(b0, sp)
    function rewrite(t, σ)
        safe_iscall(t) || return t
        args = arguments(t)
        isempty(args) && return t
        rp = radical_parts(t)
        if rp !== nothing && radicand_element(rp[2], xk) == uo
            k = 2 * rp[1]
            isone(denominator(k)) || throw(RischNotImplemented("√($uterm): radical exponent not a multiple of 1/2"))
            k = Int(numerator(k))
            return mk(b0, :^, mk(b0, :*, b0.lift(σ), st, sqc), b0.lift(k))
        end
        b0.build(op_function(t), (rewrite(a, σ) for a in args)...)
    end
    Fp = risch_integrate(rewrite(f, 1), x; build = b0.build, lift = b0.lift, verify = verify)
    Fm = risch_integrate(rewrite(f, -1), x; build = b0.build, lift = b0.lift, verify = verify)
    (Fp isa IntegralWithRootSums || Fm isa IntegralWithRootSums) && throw(RischNotImplemented(
        "√($uterm): RootSums on the branches of a square radicand"))
    σ = mk(b0, :/, mk(b0, :/, mk(b0, :sqrt, uterm), st), sqc)
    half = b0.lift(Q(1, 2))
    mk(b0, :+, mk(b0, :*, half, mk(b0, :+, Fp, Fm)), mk(b0, :*, half, σ, mk(b0, :+, Fp, mk(b0, :*, b0.lift(-1), Fm))))
end

# step SQ, index n ≥ 3 (see the caller): nothing when u is not of that shape
function integrate_root_repeated(f, xk::String, u, uterm, n::Int, b0::Builder, verify::Bool)
    P = UPoly{Q}
    N = u.num
    sf = squarefree(N)
    any(((_, m),) -> m >= n, sf) || length(sf) >= 2 || return nothing
    s = prod((p^(m ÷ n) for (p, m) in sf); init = one(P))
    rest = [(p, m % n) for (p, m) in sf if m % n != 0]
    lin = Tuple{Q,Int}[]                                # (root, multiplicity) of the linear factors left
    for (p, m) in rest
        for g in factor_Q(p)
            degree(g) == 1 || return nothing
            push!(lin, (-g.c[1], m))
        end
    end
    c = lc(N)
    if length(lin) == 1
        (a, j), bq, k = lin[1], nothing, 0
    elseif length(lin) == 2 && (lin[1][2] + lin[2][2]) % n == 0
        (a, j), (bq, k) = lin[1], lin[2]
    else
        return nothing
    end
    gcd(j, n) == 1 || return nothing
    cr = rat_root(c, n)                                 # u = c·sⁿ·(x - a)ʲ(x - b)ᵏ: c must be an n-th power
    cr === nothing && return nothing
    jinv = invmod(j, n)
    e0 = (j * jinv - 1) ÷ n
    tt = frac(xpoly(Q))
    kq(q) = frac(P(Q[q]))
    tn = tt^n
    # v = (x - a)/(x - b) (or v = x - a): x = φ(t)
    φ = bq === nothing ? tn + kq(a) : (kq(-a) + kq(bq) * tn) / (tn - kq(1))
    xa, xb = φ - kq(a), bq === nothing ? one(φ) : φ - kq(bq)
    sφ = sum((φ^(i - 1) * kq(cf) for (i, cf) in enumerate(s.c)); init = zero(φ))
    q = bq === nothing ? 0 : (j + k) ÷ n
    # u^(p/n) = (cr s (x - b)^q)^p t^(p j)
    radval = function (ue, e)
        ue == u || throw(RischError("unexpected radicand"))
        pn = e * n
        isone(denominator(pn)) || throw(RischError("radical exponent not a multiple of 1/n"))
        p = Int(numerator(pn))
        (kq(cr) * sφ * xb^q)^p * tt^(p * j)
    end
    # t printed through u^(1/n): T = u^(1/n)/(cr s (x - b)^q) = tʲ, t = T^j′ / v^e0 (j j′ = 1 + n e0)
    xt = b0.x
    vterm = bq === nothing ? mk(b0, :+, xt, cterm(b0, -a)) :
            mk(b0, :/, mk(b0, :+, xt, cterm(b0, -a)), mk(b0, :+, xt, cterm(b0, -bq)))
    den = mk(b0, :*, cterm(b0, cr), poly_term(b0, s))
    q > 0 && (den = mk(b0, :*, den, mk(b0, :^, mk(b0, :+, xt, cterm(b0, -bq)), b0.lift(q))))
    T = mk(b0, :/, mk(b0, :^, uterm, b0.lift(Q(1, n))), den)
    tterm = jinv == 1 ? T : mk(b0, :^, T, b0.lift(jinv))
    e0 > 0 && (tterm = mk(b0, :/, tterm, mk(b0, :^, vterm, b0.lift(e0))))
    try_substitutions(f, xk, Any[(Q, φ, radval, tterm, Any[])], b0, verify)
end
