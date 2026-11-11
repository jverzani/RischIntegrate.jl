# ---------------------------------------------------------------------------
# Step TX: products of sines and cosines of rational multiples of one frequency ω, over a power of x
#     f = K x^(-m) Π trigⱼ(rⱼ ω x)^(kⱼ),   trig ∈ {sin, cos}, rⱼ ∈ ℚ, m ≥ 1,   K free of x
# (the Borwein integrals Π sin(x/(2j-1))/(x/(2j-1)), or with sinc(u) = sin(πu)/(πu), ω = π). The tower route
# takes exp(i ω x/L) with L = lcm of the denominators (45045 for eight factors) and powers of it in the thousands;
# here the product goes to a sum by the product-to-sum identities (at most 2^(n-1) terms with frequencies
# ±r₁ ± r₂ ± …), and each term by parts:
#     ∫ cos(cx)/xᵐ = -cos(cx)/((m-1)x^(m-1)) - c/(m-1) ∫ sin(cx)/x^(m-1)
#     ∫ sin(cx)/xᵐ = -sin(cx)/((m-1)x^(m-1)) + c/(m-1) ∫ cos(cx)/x^(m-1)
#     ∫ sin(cx)/x = Si(cx),  ∫ cos(cx)/x = Ci(cx) (c > 0),  ∫ 1/xᵐ = log x or x^(1-m)/(1-m)
# with c = rω (ω > 0: a parameter or π). The answer is checked numerically (Si, Ci real-only, see
# `numeric_evaluator`). Nothing when f is not of this form.
# ---------------------------------------------------------------------------

const TX_MAX_TERMS = 4096

# sinc(u) = sin(πu)/(πu), Julia's (normalized) sinc, as Base and SymJ define it; f rewritten so, or nothing
function rewrite_sinc(f, x, build, lift)
    @nospecialize f x
    has_op(f, :sinc) || return nothing
    bd = Builder(build === nothing ? auto_build(f, x) : build, lift === nothing ? auto_lift(f, x) : lift, x)
    function rw(t)
        isnode(t) || return t
        args = Any[rw(a) for a in arguments(t)]
        if opname(operation(t)) === :sinc && length(args) == 1
            πu = mk(bd, :*, bd.lift(π), args[1])
            return mk(bd, :/, mk(bd, :sin, πu), πu)
        end
        term_rebuild(bd, t, args)
    end
    rw(f)
end

function integrate_trig_products(f, x; build = nothing, lift = nothing, verify::Bool = true)
    @nospecialize f x
    xk = string(x)
    bd = Builder(build === nothing ? auto_build(f, x) : build, lift === nothing ? auto_lift(f, x) : lift, x)
    # the factors: x^e, trig(a x)^k (k ≥ 1, a free of x), and x-free ones (K)
    m = 0
    Kf = Tuple{Any,Int}[]                               # (b, e), built only once f is of this form
    trigs = Tuple{Symbol,Any,Int}[]                     # (:sin/:cos, a, k)
    for (b, e) in product_factors!(Any[], f, 1)
        if !has_x(b, xk)
            push!(Kf, (b, e))
        elseif !isnode(b) && string(b) == xk
            m -= e
        elseif isnode(b) && opname(operation(b)) in (:sin, :cos) && length(arguments(b)) == 1 && e >= 1
            pp = poly_parts(bd, arguments(b)[1], xk)
            (pp === nothing || keys(pp) != Set([1])) && return nothing
            push!(trigs, (opname(operation(b)), pp[1], e))
        else
            return nothing
        end
    end
    (m >= 1 && sum((k for (_, _, k) in trigs); init = 0) >= 2) || return nothing
    # the x-free factors: numbers into one rational (a term type that evaluates integer powers, SymbolicUtils, raises
    # a DomainError for 2^-1), the rest as powers
    Kq = Q(1)
    K = Any[]
    for (b, e) in Kf
        q = leaf_rational(b)
        if q !== nothing && !iszero(q)
            Kq *= Q(q)^e
        else
            push!(K, e == 1 ? b : mk(bd, :^, b, bd.lift(e)))
        end
    end
    isone(Kq) || pushfirst!(K, cterm(bd, Kq))
    # the frequencies as rational multiples rⱼ of ω = the first one; a rational ω (x/1, x/3) folded into the rⱼ, so that
    # the answer has sin(7//15 x), not 1^-1 factors (which evaluate in Float64)
    qval(t) = try
        T, el = build_tower(t, xk)
        (isempty(T.levels) && degree(el.num) <= 0 && degree(el.den) == 0) ? rational_const(el.num.c[1] / el.den.c[1]) : nothing
    catch err
        (err isa RischNotImplemented || err isa RischError) || rethrow()
        nothing
    end
    ω = trigs[1][2]
    ωq = qval(ω)
    ratio(a) = ωq === nothing ? qval(mk(bd, :/, a, ω)) : qval(a)
    ωq === nothing || (ω = bd.lift(1))
    # the product as Σ w trig(r ω x), r ≥ 0: Dict (kind, r) => w
    S = Dict{Tuple{Symbol,Q},Q}((:cos, Q(0)) => Q(1))
    add!(d, kind, r, w) = begin
        if r < 0
            r = -r
            kind === :sin && (w = -w)
        end
        (kind === :sin && iszero(r)) && return d
        k = (kind, r)
        v = get(d, k, Q(0)) + w
        iszero(v) ? delete!(d, k) : (d[k] = v)
        d
    end
    for (kind, a, k) in trigs
        r = ratio(a)
        r === nothing && return nothing
        for _ in 1:k
            S2 = Dict{Tuple{Symbol,Q},Q}()
            for ((k1, r1), w) in S
                h = w / 2
                if k1 === :cos && kind === :cos          # cos A cos B = (cos(A - B) + cos(A + B))/2
                    add!(S2, :cos, r1 - r, h); add!(S2, :cos, r1 + r, h)
                elseif k1 === :sin && kind === :sin      # sin A sin B = (cos(A - B) - cos(A + B))/2
                    add!(S2, :cos, r1 - r, h); add!(S2, :cos, r1 + r, -h)
                elseif k1 === :sin                       # sin A cos B = (sin(A + B) + sin(A - B))/2
                    add!(S2, :sin, r1 + r, h); add!(S2, :sin, r1 - r, h)
                else                                     # cos A sin B = (sin(A + B) - sin(A - B))/2
                    add!(S2, :sin, r1 + r, h); add!(S2, :sin, r1 - r, -h)
                end
            end
            S = S2
            length(S) > TX_MAX_TERMS && return nothing
        end
    end
    # ∫ Σ w trig(rωx)/xᵐ: blocks (kind, r, k) for trig(rωx)/xᵏ (k ≥ 1), (:Si, r), (:Ci, r), (:log, 0), (:pow, k) for
    # x^(1-k)/(1-k) ... each with Σ (Q coefficient) ω^p, kept as Dict block => Dict p => Q
    out = Dict{Tuple{Symbol,Q,Int},Dict{Int,Q}}()
    acc!(blk, p, c) = (iszero(c) || (d = get!(out, blk, Dict{Int,Q}()); v = get(d, p, Q(0)) + c;
                                    iszero(v) ? delete!(d, p) : (d[p] = v)))
    function integ(kind, r, mm, c, p)                   # c ω^p ∫ trig(rωx)/x^mm
        if iszero(r)                                     # (cos 0 = 1)
            mm == 1 ? acc!((:log, Q(0), 0), p, c) : acc!((:pow, Q(0), mm), p, c / (1 - mm))
            return
        end
        if mm == 1
            acc!((kind === :sin ? :Si : :Ci, r, 0), p, c)
            return
        end
        acc!((kind, r, mm - 1), p, -c / (mm - 1))
        # ∓ c r/(mm - 1) ω^(p+1) ∫ (sin|cos)(rωx)/x^(mm-1)
        if kind === :cos
            integ(:sin, r, mm - 1, -c * r / (mm - 1), p + 1)
        else
            integ(:cos, r, mm - 1, c * r / (mm - 1), p + 1)
        end
    end
    for ((kind, r), w) in S
        integ(kind, r, m, w, 0)
    end
    X = bd.x
    pw(t, k) = k == 1 ? t : mk(bd, :^, t, bd.lift(k))
    ωp(p) = (p == 0 || ωq !== nothing) ? nothing : pw(ω, p)
    cx(r) = ωq !== nothing ? (isone(r) ? X : mk(bd, :*, cterm(bd, r), X)) :
            isone(r) ? mk(bd, :*, ω, X) : mk(bd, :*, cterm(bd, r), ω, X)
    terms = Any[]
    for (blk, cs) in sort!(collect(out); by = b -> (string(b[1][1]), b[1][2], b[1][3]))
        kind, r, k = blk
        isempty(cs) && continue
        coef = Any[]
        for (p, c) in sort!(collect(cs); by = first)
            t = ωp(p)
            push!(coef, t === nothing ? cterm(bd, c) : isone(c) ? t : mk(bd, :*, cterm(bd, c), t))
        end
        ct = length(coef) == 1 ? coef[1] : mk(bd, :+, coef...)
        body = kind === :Si ? mk(bd, :Si, cx(r)) : kind === :Ci ? mk(bd, :Ci, cx(r)) :
               kind === :log ? mk(bd, :log, X) : kind === :pow ? pw(X, 1 - k) :
               mk(bd, :/, mk(bd, kind, cx(r)), pw(X, k))
        push!(terms, mk(bd, :*, ct, body))
    end
    isempty(terms) && return nothing
    G = length(terms) == 1 ? terms[1] : mk(bd, :+, terms...)
    isempty(K) || (G = mk(bd, :*, K..., G))
    (verify && !tx_check(f, G, xk)) && return nothing
    G
end

# G′ = f numerically at points away from 0: near 0 the terms of G, of order x^(1-m) with coefficients up to (Σ rⱼ)^m,
# cancel to O(1), beyond Float64's central difference for m ≥ 6 (the formulas themselves are exact)
function tx_check(f, G, xk::String)
    ev = numeric_evaluator(xk, f, G)
    found = 0
    for x0 in (2.3, 3.7, 5.9, 9.1)
        fv, dG = try
            h = 1e-5 * x0
            ev(f, x0), (ev(G, x0 + h) - ev(G, x0 - h)) / (2h)
        catch
            continue
        end
        (isfinite(fv) && isfinite(dG)) || continue
        abs(dG - fv) <= 1e-5 * max(1.0, abs(fv)) || return false
        found += 1
    end
    found > 0
end
