# ---------------------------------------------------------------------------
# Step HS: ∫ c xᵐ (α + β xⁿ)^q with a symbolic exponent m or q (α, β free of x, possibly symbolic; n an integer),
# as for numeric exponents (step H1),
#   ∫ xᵐ (α + β xⁿ)^q dx = α^q x^(m+1)/(m+1) ₂F₁(-q, (m+1)/n; (m+1)/n + 1; -β xⁿ/α)
# (termwise; a symbolic m ≠ -1 is taken for granted, as Rubi does). For m = -1 (q symbolic), with w = 1 + βxⁿ/α,
# ∫ (α + βxⁿ)^q/x dx = (α^q/n) ∫ w^q/(w - 1) dw, which is, expanding in 1/w resp. w,
#   (α + βxⁿ)^q/(n q) ₂F₁(1, -q; 1 - q; α/(α + βxⁿ))                     (βxⁿ/α > 0: 0 < α/(α + βxⁿ) < 1)
#   -(α + βxⁿ)^(q+1)/(n α (q+1)) ₂F₁(1, q + 1; q + 2; 1 + βxⁿ/α)         (-1 < βxⁿ/α < 0),
# the second when β/α is a negative rational ((1 - eˣ)^q), else the first ((1 + eˣ)^q, (a + b eˣ)^q). Rubi 1508,
# 1513, 1520 (after u = eˣ). The ₂F₁ is a term (HypergeometricFunctions._₂F₁);
# a term type without it goes through the special-function fallback. Rubi 1164, 1171, 1183.
# ---------------------------------------------------------------------------
OPS[:_₂F₁] = _₂F₁

# an exponent: rational part + symbolic terms
mutable struct SymExp
    r::Q
    ts::Vector{Any}
end
symbolic(s::SymExp) = !isempty(s.ts)
function exp_term(bd::Builder, s::SymExp)
    ts = Any[t for t in s.ts]
    iszero(s.r) || push!(ts, cterm(bd, s.r))
    isempty(ts) ? bd.lift(0) : length(ts) == 1 ? ts[1] : mk(bd, :+, ts...)
end
function add_exp!(bd::Builder, s::SymExp, E, e::Int)  # s += e·E
    r = leaf_rational(E)
    if r !== nothing
        s.r += e * Q(r)
    else
        push!(s.ts, e == 1 ? E : mk(bd, :*, bd.lift(e), E))
    end
    s
end

# α + β xⁿ as (α, β, n) terms (α, β free of x), else nothing
function binomial_parts(bd::Builder, B, xk::String)
    (safe_iscall(B) && opname(operation(B)) in (:+, :-)) || return nothing
    args = arguments(B)
    terms = opname(operation(B)) === :+ ? Any[a for a in args] :
            length(args) == 2 ? Any[args[1], mk(bd, :*, bd.lift(-1), args[2])] : nothing
    terms === nothing && return nothing
    αs, mono = Any[], nothing
    for t in terms
        if !depends_on(t, xk)
            push!(αs, t)
            continue
        end
        mono === nothing || return nothing
        βs, n = Any[], 0
        for (s, e) in product_factors!(Any[], t, 1)
            if !depends_on(s, xk)
                push!(βs, e == 1 ? s : mk(bd, :^, s, bd.lift(e)))
            elseif !safe_iscall(s) && string(s) == xk
                n += e
            else
                return nothing
            end
        end
        n >= 1 || return nothing
        mono = (isempty(βs) ? bd.lift(1) : length(βs) == 1 ? βs[1] : mk(bd, :*, βs...), n)
    end
    (mono === nothing || isempty(αs)) && return nothing
    (length(αs) == 1 ? αs[1] : mk(bd, :+, αs...), mono[1], mono[2])
end

function try_binomial_symbolic(f, x; build = nothing, lift = nothing, verify::Bool = true)
    @nospecialize f x
    xk = string(x)
    bd = Builder(build === nothing ? auto_build(f, x) : build, lift === nothing ? auto_lift(f, x) : lift, x)
    m, q = SymExp(Q(0), Any[]), SymExp(Q(0), Any[])
    cs, B = Any[], nothing
    for (t, e) in product_factors!(Any[], f, 1)
        if !depends_on(t, xk)
            push!(cs, e == 1 ? t : mk(bd, :^, t, bd.lift(e)))
            continue
        end
        base, E = t, nothing                            # t = base^E, E free of x (not rational: a symbolic power)
        if safe_iscall(t) && opname(operation(t)) === :^ && length(arguments(t)) == 2 && !depends_on(arguments(t)[2], xk)
            base, E = arguments(t)
        end
        if !safe_iscall(base) && string(base) == xk
            E === nothing ? (m.r += e) : add_exp!(bd, m, E, e)
        else
            (B === nothing || string(B) == string(base)) || return nothing
            B = base
            E === nothing ? (q.r += e) : add_exp!(bd, q, E, e)
        end
    end
    (B !== nothing && (symbolic(m) || symbolic(q))) || return nothing
    parts = binomial_parts(bd, B, xk)
    parts === nothing && return nothing
    α, β, n = parts
    !symbolic(m) && m.r == -1 && return binomial_over_x(bd, f, cs, α, β, n, q)
    m1 = SymExp(m.r + 1, m.ts)
    m1t = exp_term(bd, m1)
    qt = exp_term(bd, q)
    isunit(t) = (r = leaf_rational(t); r !== nothing && isone(r))
    a = n == 1 ? m1t : mk(bd, :/, m1t, bd.lift(n))
    xn = n == 1 ? bd.x : mk(bd, :^, bd.x, bd.lift(n))
    βxn = isunit(β) ? xn : mk(bd, :*, β, xn)
    z = mk(bd, :*, bd.lift(-1), isunit(α) ? βxn : mk(bd, :/, βxn, α))
    F21 = hyp2f1_term(bd, f, exp_term(bd, SymExp(-q.r, Any[mk(bd, :*, bd.lift(-1), t) for t in q.ts])), a,
                      mk(bd, :+, a, bd.lift(1)), z)
    fs = Any[t for t in cs if !isunit(t)]
    isunit(α) || push!(fs, mk(bd, :^, α, qt))
    push!(fs, mk(bd, :/, mk(bd, :^, bd.x, m1t), m1t), F21)
    mk(bd, :*, fs...)
end

function hyp2f1_term(bd::Builder, f, args...)
    try
        mk(bd, :_₂F₁, args...)
    catch err                                           # (SymEngine: _₂F₁ tries to evaluate its arguments)
        (f isa Expr || err isa MethodError) && rethrow()
        throw(MethodError(_₂F₁, args))                  # the special-function fallback, through Expr
    end
end

# ∫ c (α + β xⁿ)^q / x, q symbolic (see the header)
function binomial_over_x(bd::Builder, f, cs, α, β, n::Int, q::SymExp)
    symbolic(q) || return nothing
    isunit(t) = (r = leaf_rational(t); r !== nothing && isone(r))
    xn = n == 1 ? bd.x : mk(bd, :^, bd.x, bd.lift(n))
    βxn = isunit(β) ? xn : mk(bd, :*, β, xn)
    b = mk(bd, :+, α, βxn)                              # α + β xⁿ
    qt = exp_term(bd, q)
    rα, rβ = leaf_rational(α), leaf_rational(β)
    fs = Any[t for t in cs if !isunit(t)]
    if rα !== nothing && rβ !== nothing && Q(rβ) / Q(rα) < 0
        q1 = exp_term(bd, SymExp(q.r + 1, q.ts))
        F21 = hyp2f1_term(bd, f, bd.lift(1), q1, exp_term(bd, SymExp(q.r + 2, q.ts)),
                          mk(bd, :+, bd.lift(1), isunit(α) ? βxn : mk(bd, :/, βxn, α)))
        den = mk(bd, :*, cterm(bd, Q(-n) * Q(rα)), q1)
        push!(fs, mk(bd, :/, mk(bd, :^, b, q1), den), F21)
    else
        mq = exp_term(bd, SymExp(-q.r, Any[mk(bd, :*, bd.lift(-1), t) for t in q.ts]))
        F21 = hyp2f1_term(bd, f, bd.lift(1), mq, exp_term(bd, SymExp(1 - q.r, Any[mk(bd, :*, bd.lift(-1), t) for t in q.ts])),
                          mk(bd, :/, α, b))
        push!(fs, mk(bd, :/, mk(bd, :^, b, qt), n == 1 ? qt : mk(bd, :*, bd.lift(n), qt)), F21)
    end
    mk(bd, :*, fs...)
end
