# ---------------------------------------------------------------------------
# Step AN: the arguments of exp, sin, cos, sinh, cosh and of a power b^u (b free of x), normalized after a
# NotElementary:
#  * a quotient P/Q of polynomials in x with deg Q = 1 and deg P ≥ 1 as S + ρ/Q, S a polynomial (by the root of Q):
#    cos((a + b x)/(c + d x)) = cos(b/d + (a d - b c)/(d (c + d x))), then the addition formulas and u = 1/(c + d x)
#    give Si, Ci (sample 2250);
#  * the part free of x of an exponent as a factor: f^(a + b/x) = f^a f^(b/x) (samples 1159, 1160, which were
#    refused for the constant f^a beside the Ei of b log(f)/x), and likewise exp(a + u) = e^a e^u.
# Returns the rewritten Expr, or nothing when nothing changed.
# ---------------------------------------------------------------------------
const AN_FUNS = (:exp, :sin, :cos, :sinh, :cosh)

# Expr arithmetic folding 0, 1 and numbers
an_isnum(a) = a isa Number
function an_mul(a, b)
    (a == 0 || b == 0) && return 0
    a == 1 && return b
    b == 1 && return a
    (an_isnum(a) && an_isnum(b)) && return a * b
    Expr(:call, :*, a, b)
end
function an_add(a, b)
    a == 0 && return b
    b == 0 && return a
    (an_isnum(a) && an_isnum(b)) && return a + b
    Expr(:call, :+, a, b)
end
an_neg(a) = an_mul(-1, a)
function an_div(a, b)
    b == 1 && return a
    a == 0 && return 0
    a == b && return 1
    Expr(:call, :/, a, b)
end

# the coefficients of e as a polynomial in xs (Dict degree => Expr), or nothing
function an_poly(e, xs::Symbol, xk::String)
    has_x(e, xk) || return Dict{Int,Any}(0 => e)
    e === xs && return Dict{Int,Any}(1 => 1)
    (e isa Expr && e.head === :call) || return nothing
    op, as = e.args[1], e.args[2:end]
    add!(D, k, c) = (D[k] = haskey(D, k) ? an_add(D[k], c) : c; D)
    if op === :+ || (op === :- && length(as) == 2)
        D = Dict{Int,Any}()
        for (j, a) in enumerate(as)
            p = an_poly(a, xs, xk); p === nothing && return nothing
            for (k, c) in p
                add!(D, k, (op === :- && j == 2) ? an_neg(c) : c)
            end
        end
        return D
    elseif op === :- && length(as) == 1
        p = an_poly(as[1], xs, xk); p === nothing && return nothing
        return Dict{Int,Any}(k => an_neg(c) for (k, c) in p)
    elseif op === :*
        D = Dict{Int,Any}(0 => 1)
        for a in as
            p = an_poly(a, xs, xk); p === nothing && return nothing
            E = Dict{Int,Any}()
            for (i, c) in D, (j, d) in p
                add!(E, i + j, an_mul(c, d))
            end
            D = E
        end
        return D
    elseif op === :^ && length(as) == 2 && as[2] isa Integer && 0 <= as[2] <= 8
        D = Dict{Int,Any}(0 => 1)
        p = an_poly(as[1], xs, xk); p === nothing && return nothing
        for _ in 1:as[2]
            E = Dict{Int,Any}()
            for (i, c) in D, (j, d) in p
                add!(E, i + j, an_mul(c, d))
            end
            D = E
        end
        return D
    end
    nothing
end

# P/Q, deg Q = 1, deg P ≥ 1 → S + ρ/Q (Horner at the root r = -q₀/q₁); else nothing
function an_divide(u, xs::Symbol, xk::String)
    (u isa Expr && u.head === :call && u.args[1] === :/ && length(u.args) == 3) || return nothing
    P, Qe = u.args[2], u.args[3]
    (has_x(P, xk) && has_x(Qe, xk)) || return nothing
    p, q = an_poly(P, xs, xk), an_poly(Qe, xs, xk)
    (p === nothing || q === nothing) && return nothing
    (maximum(keys(q)) == 1 && haskey(q, 1)) || return nothing
    n = maximum(keys(p))
    n >= 1 || return nothing
    q1, q0 = q[1], get(q, 0, 0)
    r = an_div(an_neg(q0), q1)
    cf(k) = get(p, k, 0)
    s = Vector{Any}(undef, n)                         # P = (x - r) Σ s_k x^k + ρ
    s[n] = cf(n)
    for k in n-1:-1:1
        s[k] = an_add(cf(k), an_mul(r, s[k+1]))
    end
    ρ = an_add(cf(0), an_mul(r, s[1]))
    S = Any[an_div(k == 1 ? s[k] : an_mul(s[k], k == 2 ? xs : Expr(:call, :^, xs, k - 1)), q1) for k in 1:n]
    Expr(:call, :+, S..., an_div(ρ, Qe))
end

# e = c + v with c the terms free of x and v not a polynomial in x (else nothing)
function an_split_const(e, xk::String)
    (e isa Expr && e.head === :call && e.args[1] === :+) || return nothing
    as = e.args[2:end]
    cs, vs = filter(a -> !has_x(a, xk), as), filter(a -> has_x(a, xk), as)
    (isempty(cs) || isempty(vs)) && return nothing
    v = length(vs) == 1 ? vs[1] : Expr(:call, :+, vs...)
    an_poly(v, Symbol(xk), xk) === nothing || return nothing   # (a polynomial exponent: the tower takes e^c itself)
    (length(cs) == 1 ? cs[1] : Expr(:call, :+, cs...)), v
end

function normalize_function_args(f, xs)
    xs = xs isa Symbol ? xs : Symbol(string(xs))
    xk = string(xs)
    changed = false
    function rw(e)
        e isa Expr || return e
        args = Any[rw(a) for a in e.args]
        if e.head === :call && length(args) == 2 && args[1] in AN_FUNS && has_x(args[2], xk)
            u = args[2]
            d = an_divide(u, xs, xk)
            d === nothing || (changed = true; u = d)
            if args[1] === :exp
                cv = an_split_const(u, xk)
                if cv !== nothing
                    changed = true
                    return Expr(:call, :*, Expr(:call, :exp, cv[1]), Expr(:call, :exp, cv[2]))
                end
            end
            return Expr(:call, args[1], u)
        elseif e.head === :call && length(args) == 3 && args[1] === :^ && !has_x(args[2], xk) && has_x(args[3], xk)
            u = args[3]
            d = an_divide(u, xs, xk)
            d === nothing || (changed = true; u = d)
            cv = an_split_const(u, xk)
            if cv !== nothing
                changed = true
                return Expr(:call, :*, Expr(:call, :^, args[2], cv[1]), Expr(:call, :^, args[2], cv[2]))
            end
            return Expr(:call, :^, args[2], u)
        end
        # two factors sin, cos of distinct linear arguments as a sum (cos(a + b x) cos(c + d x)/(c + d x), after step
        # EF by parts on Ci(c + d x) sin(a + b x), sample 2952)
        if e.head === :call && (args[1] === :* || args[1] === :/)
            # (the product flattened through *, / and unary -: (-cos(b x)/b) cos(x)/x)
            nu, de = Any[], Any[]
            function fl(t, up)
                if t isa Expr && t.head === :call && t.args[1] === :*
                    foreach(z -> fl(z, up), t.args[2:end])
                elseif t isa Expr && t.head === :call && t.args[1] === :/ && length(t.args) == 3
                    fl(t.args[2], up); fl(t.args[3], !up)
                elseif t isa Expr && t.head === :call && t.args[1] === :- && length(t.args) == 2
                    push!(nu, -1); fl(t.args[2], up)
                else
                    push!(up ? nu : de, t)
                end
            end
            fl(Expr(:call, args...), true)
            fa = isempty(de) ? Any[:*, nu...] : Any[:*, nu..., Expr(:call, :/, 1, length(de) == 1 ? de[1] : Expr(:call, :*, de...))]
            r = an_product_to_sum(fa, xs, xk)
            r === nothing || (changed = true; return r)
        end
        Expr(e.head, args...)
    end
    g = rw(f)
    changed ? g : nothing
end

# args = [:*, factors...]: two factors sin, cos (or sinh, cosh) of distinct linear arguments by the product formulas,
# else nothing
function an_product_to_sum(args, xs, xk)
        if length(args) >= 3
            it = findall(z -> z isa Expr && z.head === :call && length(z.args) == 2 && z.args[1] in (:sin, :cos, :sinh, :cosh) &&
                              (p = an_poly(z.args[2], xs, xk); p !== nothing && maximum(keys(p)) == 1), args[2:end])
            if length(it) == 2
                F1, F2 = args[it[1]+1], args[it[2]+1]
                A, B = F1.args[2], F2.args[2]
                s1, s2 = F1.args[1], F2.args[1]
                hy = s1 in (:sinh, :cosh)
                if A != B && hy == (s2 in (:sinh, :cosh))
                    pa, pb = an_poly(A, xs, xk), an_poly(B, xs, xk)
                    lin(c0, c1) = an_add(c0, an_mul(c1, xs))
                    m = lin(an_add(get(pa, 0, 0), an_neg(get(pb, 0, 0))), an_add(get(pa, 1, 0), an_neg(get(pb, 1, 0))))
                    p = lin(an_add(get(pa, 0, 0), get(pb, 0, 0)), an_add(get(pa, 1, 0), get(pb, 1, 0)))
                    (t1, σ, t2) = s1 === :cos && s2 === :cos ? (:(cos($m)), 1, :(cos($p))) :
                                  s1 === :sin && s2 === :sin ? (:(cos($m)), -1, :(cos($p))) :
                                  s1 === :sin ? (:(sin($p)), 1, :(sin($m))) :
                                  s1 === :cos ? (:(sin($p)), -1, :(sin($m))) :
                                  s1 === :cosh && s2 === :cosh ? (:(cosh($p)), 1, :(cosh($m))) :
                                  s1 === :sinh && s2 === :sinh ? (:(cosh($p)), -1, :(cosh($m))) :
                                  s1 === :sinh ? (:(sinh($p)), 1, :(sinh($m))) : (:(sinh($p)), -1, :(sinh($m)))
                    rest = Any[args[j] for j in 2:length(args) if j != it[1] + 1 && j != it[2] + 1]
                    return Expr(:call, :+, Expr(:call, :*, 1 // 2, t1, rest...), Expr(:call, :*, σ // 2, t2, rest...))
                end
            end
        end
        nothing
end

integrate_normalized_args(f, x; build = nothing, lift = nothing, verify::Bool = true) =
    integrate_rewritten_expr(f, x, normalize_function_args, AN_ACTIVE; build = build, lift = lift, verify = verify)
