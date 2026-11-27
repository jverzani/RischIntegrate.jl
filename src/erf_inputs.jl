# ---------------------------------------------------------------------------
# Step EF: integrands with erf, erfi, erfc, FresnelS, FresnelC of one linear argument u = a x + b (Rubi 8.1, 8.2;
# samples 2926–2940), after step ER (one erf or erfi to the first power, by parts) refuses. With F the function and
# F′(u) its derivative (2/√π e^(-u²), 2/√π e^(u²), sin(π u²/2), cos(π u²/2)); erfc = 1 - erf:
#   derivative-divides: f = g(F(u)) a F′(u) with g free of x (e^(c - b² x²) erf(b x)ⁿ, e^(c - b² x²)/erfc(b x),
#     cos(π b² x²/2) FresnelC(b x)): ∫ f = G(F(u)), G = ∫ g(t) dt;
#   by parts: f = A F(u)ᵏ with A free of F: Q F(u)ᵏ - k ∫ Q F(u)ᵏ⁻¹ a F′(u), Q = ∫ A (Q = u/a for A = 1); the
#     second integral by this step again (erf(u)²: ∫ u erf(u) e^(-u²)), or step GT, GQ (∫ Q sin(π u²/2)).
# Answers checked numerically, FresnelS and FresnelC written with erf for the check:
#   S(z) = (1 + i)/4 [erf((1 + i)√π z/2) - i erf((1 - i)√π z/2)],  C(z) = (1 - i)/4 [erf((1 + i)√π z/2) + i erf((1 - i)√π z/2)].
# By parts nests twice at most (step ER's depth). Nothing when f has another such function or another argument.
# ---------------------------------------------------------------------------
const EF_FUNS = (:erf, :erfi, :erfc, :FresnelS, :FresnelC, :fresnels, :fresnelc)

function try_erf_inputs(f, x; build = nothing, lift = nothing, verify::Bool = true)
    @nospecialize f x
    hasF(t) = isnode(t) && (opname(operation(t)) in EF_FUNS || any(hasF, arguments(t)))
    hasF(f) || return nothing
    integrate_rewritten_expr(f, x, (fe, xs) -> nothing, nothing; build = build, lift = lift, verify = verify,
                             answer = (fe, xs) -> erf_inputs_expr(fe, xs; verify = verify))
end

# FresnelS, FresnelC in erf form (for the numeric check)
function fresnel_as_erf(t)
    t isa Expr || return t
    a = Any[fresnel_as_erf(s) for s in t.args]
    if t.head === :call && length(a) == 2 && a[1] in (:FresnelS, :FresnelC, :fresnels, :fresnelc)
        z = a[2]
        p = :(erf((1 + im) * sqrt(π) * $z / 2))
        m = :(erf((1 - im) * sqrt(π) * $z / 2))
        return a[1] in (:FresnelS, :fresnels) ? :((1 + im) / 4 * ($p - im * $m)) : :((1 - im) / 4 * ($p + im * $m))
    end
    Expr(t.head, a...)
end

function erf_inputs_expr(fe, xs::Symbol; verify::Bool = true)
    xk = string(xs)
    ERF_DEPTH[] >= 2 && return nothing
    isF(t) = t isa Expr && t.head === :call && length(t.args) == 2 && t.args[1] in EF_FUNS && has_x(t.args[2], xk)
    rep(t, a, b) = t == a ? b : t isa Expr ? Expr(t.head, (rep(s, a, b) for s in t.args)...) : t
    # erfc(u) = 1 - erf(u)
    noc(t) = t isa Expr ? (isF(t) && t.args[1] === :erfc ? :(1 + -1 * erf($(noc(t.args[2])))) : Expr(t.head, (noc(s) for s in t.args)...)) : t
    f = noc(fe)
    Fs = Any[]
    walk(t) = t isa Expr && (isF(t) ? (any(==(t), Fs) || push!(Fs, t)) : foreach(walk, t.args))
    walk(f)
    length(Fs) == 1 || return nothing
    Fu = Fs[1]
    name, u = Fu.args[1], Fu.args[2]
    has_x(u, xk) || return nothing
    tw(t, v) = try
        build_tower(t, v)
    catch err
        (err isa RischNotImplemented || err isa RischError || err isa NeedComplex || err isa DivideError || err isa NewConstants) || rethrow()
        (nothing, nothing)
    end
    ct(T, c, v) = cterm_complex(Builder(expr_build, identity, v, T.consts), c, T.consts)
    # u′: a constant for u = a x + b (Q = u/a for A = 1), else its derivative (erfi(d (a + b log(c xⁿ))), sample 2931)
    Tu, eu = tw(u, xk)
    lin = Tu !== nothing && isempty(Tu.levels) && degree(eu.den) == 0 && degree(eu.num) == 1
    if lin
        a = ct(Tu, eu.num.c[2] / eu.den.c[1], xs)
        b0 = ct(Tu, eu.num.c[1] / eu.den.c[1], xs)
    else
        a = term_deriv(Builder(expr_build, identity, xs), u, xk)
        a === nothing && return nothing
        # (rational in x through the tower: d b (c n xⁿ/x)/(c xⁿ) as d b n/x)
        Ta, ea = tw(a, xk)
        (Ta !== nothing && isempty(Ta.levels)) && (a = tower_to_term(Builder(expr_build, identity, xs, Ta.consts), Ta, ea))
        b0 = nothing
    end
    dF = name === :erf ? :(2 / sqrt(π) * exp(-($u) ^ 2)) : name === :erfi ? :(2 / sqrt(π) * exp(($u) ^ 2)) :
         name in (:FresnelS, :fresnels) ? :(sin(π * ($u) ^ 2 / 2)) : :(cos(π * ($u) ^ 2 / 2))
    D = leaf_rational(a) == 1 ? dF : :($a * $dF)
    check(G) = !verify || numeric_antiderivative(fresnel_as_erf(f), fresnel_as_erf(noc(G)), xk)   # (erfc as 1 - erf)
    integ(g, v) = try
        r = risch_integrate(g, v; build = expr_build, lift = identity, verify = verify)
        r isa IntegralWithRootSums ? nothing : r
    catch err
        (err isa RischNotImplemented || err isa NotElementary) || rethrow()
        nothing
    end
    ERF_DEPTH[] += 1
    try
        # derivative-divides: f/(a F′(u)) with F(u) = t free of x
        t = gensym("t")
        # (exp(c - b² x²): e^c apart, and functions of the parameters as symbols, which the tower takes)
        function splitexp(v)
            v isa Expr || return v
            w = Expr(v.head, (splitexp(z) for z in v.args)...)
            if w.head === :call && w.args[1] === :exp && length(w.args) == 2 && w.args[2] isa Expr &&
               w.args[2].head === :call && w.args[2].args[1] === :+
                fr = [z for z in w.args[2].args[2:end] if !has_x(z, xk)]
                xd = [z for z in w.args[2].args[2:end] if has_x(z, xk)]
                (isempty(fr) || isempty(xd)) && return w
                return :(exp($(Expr(:call, :+, fr...))) * exp($(Expr(:call, :+, xd...))))
            elseif w.head === :call && w.args[1] === :exp && length(w.args) == 2 && w.args[2] isa Expr &&
                   w.args[2].head === :call && w.args[2].args[1] === :- && length(w.args[2].args) == 3
                p1, p2 = w.args[2].args[2], w.args[2].args[3]
                (!has_x(p1, xk) && has_x(p2, xk)) && return :(exp($p1) * exp(-($p2)))
            end
            w
        end
        ops = Dict{Symbol,Any}()
        # (tᵖ with p not a number, t = F(u): opaque too, put back after)
        arith(v) = !(v isa Expr) || (v.head === :call && v.args[1] in (:+, :-, :*, :/) && all(arith, v.args[2:end])) ||
                   (v.head === :call && v.args[1] === :^ && leaf_rational(v.args[3]) !== nothing && arith(v.args[2]))
        function opq(v)
            v isa Expr || return v
            if !has_x(v, xk) && !arith(v)
                k = findfirst(==(v), ops)
                k === nothing && (k = gensym("c"); ops[k] = v)
                return k
            end
            Expr(v.head, (opq(z) for z in v.args)...)
        end
        Tg, eg = tw(opq(splitexp(:($(rep(f, Fu, t)) / $D))), xk)
        if Tg !== nothing && isempty(Tg.levels) && degree(eg.num) == 0 && degree(eg.den) == 0
            gt = subst_symbols(ct(Tg, eg.num.c[1] / eg.den.c[1], xs), ops)
            if !has_x(gt, xk)
                H = integ(gt, t)
                if H !== nothing
                    G = rep(H, t, Fu)
                    check(G) && return G
                end
            end
        end
        # by parts, term by term: A F(u)ᵏ, A free of F
        terms = Any[]
        sums(t) = (t isa Expr && t.head === :call && t.args[1] === :+) ? collect(t.args[2:end]) : Any[t]
        for s in sums(expand_sum_once(f))
            facs = Any[]
            flat(v) = (v isa Expr && v.head === :call && v.args[1] === :*) ? foreach(flat, v.args[2:end]) : push!(facs, v)
            flat(s)
            k = 0
            A = Any[]
            for v in facs
                if v == Fu
                    k += 1
                elseif v isa Expr && v.head === :call && v.args[1] === :^ && v.args[2] == Fu &&
                       (p = leaf_rational(v.args[3]); p !== nothing && isinteger(p) && p >= 1)
                    k += Int(p)
                else
                    walk_has = Ref(false)
                    chk(w) = w isa Expr && (w == Fu ? (walk_has[] = true) : foreach(chk, w.args))
                    chk(v)
                    walk_has[] && return nothing
                    push!(A, v)
                end
            end
            if k == 0
                H = integ(s, xs)
                H === nothing && return nothing
                push!(terms, H)
                continue
            end
            Ae = isempty(A) ? 1 : length(A) == 1 ? A[1] : Expr(:call, :*, A...)
            Q = (isempty(A) && lin) ? (leaf_rational(b0) == 0 ? xs : :($u / $a)) : isempty(A) ? xs : integ(Ae, xs)
            Q === nothing && return nothing
            Fk = k == 1 ? Fu : :($Fu ^ $k)
            Fk1 = k == 1 ? 1 : k == 2 ? Fu : :($Fu ^ $(k - 1))
            H = integ(:($k * $Q * $Fk1 * $D), xs)
            H === nothing && return nothing
            push!(terms, :($Q * $Fk - $H))
        end
        isempty(terms) && return nothing
        G = length(terms) == 1 ? terms[1] : Expr(:call, :+, terms...)
        check(G) ? G : nothing
    finally
        ERF_DEPTH[] -= 1
    end
end

# a product with one sum factor distributed once ((c + d x) (1 - erf u) → c (1 - erf u) + d x (1 - erf u)): the
# sum's terms; otherwise t
function expand_sum_once(t)
    (t isa Expr && t.head === :call && t.args[1] === :*) || return t
    j = findfirst(v -> v isa Expr && v.head === :call && v.args[1] === :+, t.args[2:end])
    j === nothing && return t
    s = t.args[j + 1]
    rest = Any[v for (i, v) in enumerate(t.args[2:end]) if i != j]
    Expr(:call, :+, (Expr(:call, :*, rest..., v) for v in s.args[2:end])...)
end
