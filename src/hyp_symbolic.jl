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
    m = SymExp(Q(0), Any[])
    cs, bases = Any[], Tuple{Any,SymExp}[]              # (base, exponent) of the factors other than x
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
            continue
        end
        k = findfirst(((b, _),) -> string(b) == string(base), bases)
        k === nothing && (push!(bases, (base, SymExp(Q(0), Any[]))); k = length(bases))
        E === nothing ? (bases[k][2].r += e) : add_exp!(bd, bases[k][2], E, e)
    end
    any(((_, q),) -> symbolic(q), bases) || symbolic(m) || return nothing
    if length(bases) == 1
        B, q = bases[1]
        parts = binomial_parts(bd, B, xk)
        parts !== nothing && return binomial_answer(bd, f, cs, m, q, parts...)
    end
    # (p₀ + p₁x)·(A₀ + A₁x + A₂x²)^q (or without the linear factor), q symbolic: completing the square
    (iszero(m.r) && !symbolic(m)) || return nothing
    lin = nothing
    if length(bases) == 2
        k = findfirst(((b, q),) -> !symbolic(q) && isone(q.r), bases)
        k === nothing && return nothing
        lin = poly_parts(bd, bases[k][1], xk)
        (lin !== nothing && maximum(keys(lin)) == 1) || return nothing
        deleteat!(bases, k)
    end
    length(bases) == 1 || return nothing
    B, q = bases[1]
    symbolic(q) || return nothing
    A = poly_parts(bd, B, xk)
    (A !== nothing && maximum(keys(A)) == 2) || return nothing
    quadratic_answer(bd, f, cs, lin, A, q)
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

# the answer c α^q u^(m+1)/(m+1) ₂F₁(-q, (m+1)/n; (m+1)/n + 1; -βuⁿ/α), u = bd.x (x, x + x₀ or sin(kx))
function binomial_answer(bd::Builder, f, cs, m::SymExp, q::SymExp, α, β, n::Int)
    !symbolic(m) && m.r == -1 && return binomial_over_x(bd, f, cs, α, β, n, q)
    m1 = SymExp(m.r + 1, m.ts)
    m1t = exp_term(bd, m1)
    qt = exp_term(bd, q)
    isunit(t) = (r = leaf_rational(t); r !== nothing && isone(r))
    a = n == 1 ? m1t : mk(bd, :/, m1t, bd.lift(n))
    xn = n == 1 ? bd.x : mk(bd, :^, bd.x, bd.lift(n))
    rβ = leaf_rational(β)                               # -βxⁿ, a rational β folded in
    mβxn = rβ === nothing ? mk(bd, :*, bd.lift(-1), β, xn) : isone(-Q(rβ)) ? xn : mk(bd, :*, cterm(bd, -Q(rβ)), xn)
    z = isunit(α) ? mβxn : mk(bd, :/, mβxn, α)
    F21 = hyp2f1_term(bd, f, exp_term(bd, SymExp(-q.r, Any[mk(bd, :*, bd.lift(-1), t) for t in q.ts])), a,
                      mk(bd, :+, a, bd.lift(1)), z)
    fs = Any[t for t in cs if !isunit(t)]
    isunit(α) || push!(fs, mk(bd, :^, α, qt))
    push!(fs, (!symbolic(m) && iszero(m.r)) ? bd.x : mk(bd, :/, mk(bd, :^, bd.x, m1t), m1t), F21)
    length(fs) == 1 ? fs[1] : mk(bd, :*, fs...)
end

# a polynomial in x with coefficients free of x as Dict(power => coefficient term), else nothing
function poly_parts(bd::Builder, B, xk::String)
    out = Dict{Int,Any}()
    add!(k, t) = (out[k] = haskey(out, k) ? mk(bd, :+, out[k], t) : t)
    function walk(t, sgn)
        if safe_iscall(t) && opname(operation(t)) === :+
            return all(a -> walk(a, sgn), arguments(t))
        elseif safe_iscall(t) && opname(operation(t)) === :- && length(arguments(t)) == 2
            return walk(arguments(t)[1], sgn) && walk(arguments(t)[2], -sgn)
        elseif safe_iscall(t) && opname(operation(t)) === :- && length(arguments(t)) == 1
            return walk(arguments(t)[1], -sgn)
        end
        cs, n = Any[], 0
        for (s, e) in product_factors!(Any[], t, 1)
            if !depends_on(s, xk)
                push!(cs, e == 1 ? s : mk(bd, :^, s, bd.lift(e)))
            elseif !safe_iscall(s) && string(s) == xk && e >= 1
                n += e
            else
                return false
            end
        end
        sgn == -1 && push!(cs, bd.lift(-1))
        add!(n, isempty(cs) ? bd.lift(1) : length(cs) == 1 ? cs[1] : mk(bd, :*, cs...))
        true
    end
    walk(B, 1) ? out : nothing
end

# ∫ c (p₀ + p₁x) B^q, B = A₀ + A₁x + A₂x² (lin = nothing: p = 1): with x₀ = A₁/(2A₂), u = x + x₀,
# α = A₀ - A₁²/(4A₂): p₁/(2A₂) B^(q+1)/(q+1) + (p₀ - p₁x₀) ∫ (α + A₂u²)^q du (Rubi 1226, 1231)
function quadratic_answer(bd::Builder, f, cs, lin, A, q::SymExp)
    z = bd.lift(0)
    A0, A1, A2 = get(A, 0, z), get(A, 1, nothing), A[2]
    x0 = A1 === nothing ? nothing : mk(bd, :/, A1, mk(bd, :*, bd.lift(2), A2))
    α = x0 === nothing ? A0 : mk(bd, :+, A0, mk(bd, :*, bd.lift(-1), A1, x0, bd.lift(1 // 2)))
    u = x0 === nothing ? bd.x : mk(bd, :+, bd.x, x0)
    bu = Builder(bd.build, bd.lift, u, bd.consts)
    p0 = lin === nothing ? bd.lift(1) : get(lin, 0, z)
    p1 = lin === nothing ? nothing : lin[1]
    c0 = (p1 === nothing || x0 === nothing) ? p0 : mk(bd, :+, p0, mk(bd, :*, bd.lift(-1), p1, x0))
    ts = Any[binomial_answer(bu, f, Any[cs; c0], SymExp(Q(0), Any[]), q, α, A2, 2)]
    if p1 !== nothing
        q1 = exp_term(bd, SymExp(q.r + 1, q.ts))
        B = mk(bd, :+, A0, (A1 === nothing ? () : (mk(bd, :*, A1, bd.x),))..., mk(bd, :*, A2, mk(bd, :^, bd.x, bd.lift(2))))
        push!(ts, mk(bd, :*, cs..., p1, mk(bd, :/, mk(bd, :^, B, q1), mk(bd, :*, bd.lift(2), A2, q1))))
    end
    length(ts) == 1 ? ts[1] : mk(bd, :+, ts...)
end

# ∫ c sinᵖ(w) cosʳ(w), w = kx + d, p or r symbolic or not an integer (sin^(7/2) cos^(3/2), SymPy #29882), by
# u = sin w (du = k cos w dx):
#   (1/k) ∫ uᵖ (1 - u²)^((r-1)/2) du · cos^(r-1)(w)/(cos² w)^((r-1)/2)
# the last factor locally constant (1 when (r-1)/2 is an integer), as in Rubi's cos w/√(cos² w) (Rubi 350, 1371)
function try_trig_symbolic(f, x; build = nothing, lift = nothing, verify::Bool = true)
    @nospecialize f x
    xk = string(x)
    bd = Builder(build === nothing ? auto_build(f, x) : build, lift === nothing ? auto_lift(f, x) : lift, x)
    p, r = SymExp(Q(0), Any[]), SymExp(Q(0), Any[])
    cs, w = Any[], nothing
    for (t, e) in product_factors!(Any[], f, 1)
        if !depends_on(t, xk)
            push!(cs, e == 1 ? t : mk(bd, :^, t, bd.lift(e)))
            continue
        end
        base, E = t, nothing
        if safe_iscall(t) && opname(operation(t)) === :^ && length(arguments(t)) == 2 && !depends_on(arguments(t)[2], xk)
            base, E = arguments(t)
        end
        (safe_iscall(base) && opname(operation(base)) in (:sin, :cos) && length(arguments(base)) == 1) || return nothing
        a = arguments(base)[1]
        (w === nothing || string(w) == string(a)) || return nothing
        w = a
        s = opname(operation(base)) === :sin ? p : r
        E === nothing ? (s.r += e) : add_exp!(bd, s, E, e)
    end
    (w !== nothing && (symbolic(p) || symbolic(r) || !isinteger(p.r) || !isinteger(r.r))) || return nothing
    u = radicand_element(w, xk)
    (u !== nothing && isone(u.den) && degree(u.num) == 1) || return nothing
    k = u.num.c[2] / u.den.c[1]
    sw, cw = mk(bd, :sin, w), mk(bd, :cos, w)
    h = SymExp((r.r - 1) / 2, Any[mk(bd, :*, bd.lift(1 // 2), t) for t in r.ts])   # (r - 1)/2
    isone(k) || push!(cs, cterm(bd, inv(k)))
    if symbolic(h) || !isone(denominator(h.r))                                       # cos^(r-1)/(cos²)^((r-1)/2)
        push!(cs, mk(bd, :/, mk(bd, :^, cw, exp_term(bd, SymExp(r.r - 1, r.ts))),
                     mk(bd, :^, mk(bd, :^, cw, bd.lift(2)), exp_term(bd, h))))
    end
    bu = Builder(bd.build, bd.lift, sw, bd.consts)
    binomial_answer(bu, f, cs, p, h, bd.lift(1), bd.lift(-1), 2)
end
