# ---------------------------------------------------------------------------
# Step HT: atanh(u), acoth(u) by the substitution u = tanh t (coth t), after every other route has failed
# (∫ (d + e x)² atanh(x)³, ∫ atanh(x)²/(x (1 - x²)): Rubi 7.3.1, answers with Li₂, Li₃). All atanh(u) (acoth(u)) in f
# share one u = (p x + q)/(r x + s) ∈ ℚ(x) (step AL has taken the symbolic scale out: atanh(c x) ↦ atanh(y)), and f is
# rational in x apart from them. With x playing the role of t and E = e^(2x):
#   w = tanh x = (E - 1)/(E + 1)  (coth x = (E + 1)/(E - 1)),   x ↦ (q - s w)/(r w - p),   atanh(u) ↦ x,
#   dx ↦ (s p - r q)/(r w - p)² (1 - w²) dx,
# so the integrand is P(x) R(E), integrated by the usual route (step PX: residues polynomial in x). The answer is
# mapped back with x ↦ atanh(u) and e^(2k x) = ((1 + u)/(1 - u))ᵏ (((u + 1)/(u - 1))ᵏ for acoth), identities of
# analytic functions (tanh(atanh u) = u for every u), and checked numerically (zero imaginary parts as +0).
# ---------------------------------------------------------------------------

function collect_invtanh(f, xk::String, out = Any[])
    if safe_iscall(f) && !isempty(arguments(f))
        args = arguments(f)
        n = opname(operation(f))
        if n in (:atanh, :acoth) && length(args) == 1 && has_x(args[1], xk)
            push!(out, (n, args[1], f))
        else
            foreach(a -> collect_invtanh(a, xk, out), args)
        end
    end
    out
end

# f rational in x apart from the atoms atanh(u) / acoth(u) (name n, argument string us)
function rational_but_atoms(t, xk::String, n::Symbol, us::String)
    (safe_iscall(t) && !isempty(arguments(t))) || return true
    has_x(t, xk) || return true
    op, args = opname(operation(t)), arguments(t)
    (op === n && length(args) == 1 && string(args[1]) == us) && return true
    op in (:+, :-, :*, :/) && return all(a -> rational_but_atoms(a, xk, n, us), args)
    if op === :^ && length(args) == 2
        has_x(args[2], xk) && return false
        e = leaf_rational(args[2])
        return e !== nothing && isone(denominator(e)) && rational_but_atoms(args[1], xk, n, us)
    end
    false
end

function try_atanh_subst(f, x; build = nothing, lift = nothing, verify::Bool = true)
    @nospecialize f x
    ATANH_SUBST[] && return nothing
    xk = string(x)
    ats = collect_invtanh(f, xk)
    isempty(ats) && return nothing
    n, arg, atom = ats[1]
    us = string(arg)
    all(a -> a[1] === n && string(a[2]) == us, ats) || return nothing
    rational_but_atoms(f, xk, n, us) || return nothing
    u = radicand_element(arg, xk)
    (u !== nothing && degree(u.num) <= 1 && degree(u.den) <= 1) || return nothing
    P = UPoly{Q}
    co(pl, k) = k + 1 <= length(pl.c) ? pl.c[k + 1] : zero(Q)
    p, q, r, s = co(u.num, 1), co(u.num, 0), co(u.den, 1), co(u.den, 0)
    iszero(s * p - r * q) && return nothing             # (u constant)
    bd = Builder(build === nothing ? auto_build(f, x) : build, lift === nothing ? auto_lift(f, x) : lift, x)
    Et = mk(bd, :exp, mk(bd, :*, bd.lift(2), bd.x))
    bE = Builder(bd.build, bd.lift, Et)                 # rational functions of E printed with e^(2x)
    Em1, Ep1 = P(Q[-1, 1]), P(Q[1, 1])
    Nw, Dw = n === :atanh ? (Em1, Ep1) : (Ep1, Em1)
    den = scale(r, Nw) - scale(p, Dw)
    X = frac(scale(q, Dw) - scale(s, Nw), den)
    J = frac(scale(s * p - r * q, Dw * Dw - Nw * Nw), den * den)
    Xt = frac_term(bE, X)
    function sub(t)
        if safe_iscall(t) && !isempty(arguments(t))
            (opname(operation(t)) === n && string(arguments(t)[1]) == us) && return bd.x
            return term_rebuild(bd, t, Any[sub(a) for a in arguments(t)])
        end
        string(t) == xk ? Xt : t
    end
    g = mk(bd, :*, sub(f), frac_term(bE, J))
    ATANH_SUBST[] = true
    G = try
        risch_integrate(g, x; build = build, lift = lift, verify = verify)
    catch e
        (e isa RischNotImplemented || e isa NotElementary) || rethrow()
        nothing
    finally
        ATANH_SUBST[] = false
    end
    (G === nothing || G isa IntegralWithRootSums) && return nothing
    # map back: e^(2x) = Eb ∈ ℚ(x), x ↦ the atom
    Eb = n === :atanh ? frac(u.den + u.num, u.den - u.num) : frac(u.num + u.den, u.num - u.den)
    function Epow(m::Int)                               # Ebᵐ
        B = m >= 0 ? Eb : frac(Eb.den, Eb.num)
        R = frac(one(P))
        for _ in 1:abs(m)
            R = R * B
        end
        R
    end
    function back(t)
        if safe_iscall(t) && !isempty(arguments(t))
            args = arguments(t)
            if opname(operation(t)) === :exp && length(args) == 1
                e = radicand_element(args[1], xk)
                if e !== nothing && isone(e.den) && degree(e.num) == 1 && iszero(e.num.c[1])
                    c = e.num.c[2]                      # e^(c x) = Eb^(c/2)
                    isone(denominator(c)) && iseven(numerator(c)) && return frac_term(bd, Epow(Int(numerator(c)) ÷ 2))
                    isone(denominator(c)) && return mk(bd, :sqrt, frac_term(bd, Epow(Int(numerator(c)))))
                end
            end
            return term_rebuild(bd, t, Any[back(a) for a in args])
        end
        string(t) == xk ? atom : t
    end
    Gb = tidy_terms(bd, back(G), xk)
    (verify && !numeric_antiderivative(f, Gb, xk; pz = true)) && return nothing
    Gb
end
