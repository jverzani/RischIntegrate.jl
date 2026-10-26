# ---------------------------------------------------------------------------
# Step CS: nested radicals whose coefficients are in ℚ(√d) (Rubi 190, √(√2 + √x + √(2 + √8√x + 2x))), after the
# usual route has failed. A scaling x = σy (σ = 1, d, 1/d) and a normal form of the integrand over ℚ(√d) can make
# every radicand rational up to a constant factor: the radicands are written as polynomials in y and the inner
# radicals (atoms) with coefficients in ℚ(√d), and each radicand P = κ P₀ with P₀ over ℚ, κ ∈ ℚ(√d) positive, gives
# √P = √κ √P₀, √κ ∈ ℚ(√d), or √κ = √b d^(1/4) for κ = b√d (an opaque constant, step IT takes it out). With x = 2y,
#   √x = √2 √y,  √(2 + 4√y + 4y) = √2 √(1 + 2√y + 2y),  √(√2 + √2√y + √2 √(…)) = 2^(1/4) √(1 + √y + √(…)),
# whose integral is the rational case (step NS). Then y = x/σ.
# ---------------------------------------------------------------------------
const CONST_SCALING = Ref(false)                        # no nested uses

function try_const_scaling(f, x; build = nothing, lift = nothing, verify::Bool = true)
    @nospecialize f x
    CONST_SCALING[] && return nothing
    xk = string(x)
    isempty(inner_radicands(f, xk)) && return nothing
    ds = BigInt[]
    function walk(t)
        safe_iscall(t) || return
        args = arguments(t)
        isempty(args) && return
        rp = radical_parts(t)
        if rp !== nothing && !has_leaf(rp[2], xk)
            c = leaf_rational(rp[2])
            if c !== nothing && c > 0 && denominator(2 * rp[1]) == 1
                dd = sqfree_split(numerator(c) * denominator(c))[2]
                isone(dd) || push!(ds, dd)
            end
        end
        foreach(walk, args)
    end
    walk(f)
    unique!(ds)
    length(ds) == 1 || return nothing
    d = Int(ds[1])
    bd = Builder(build === nothing ? auto_build(f, x) : build, lift === nothing ? auto_lift(f, x) : lift, x)
    for σ in (Q(1), Q(d), Q(1) // d)
        g = const_scaled(f, xk, d, σ, bd)
        g === nothing && continue
        CONST_SCALING[] = true
        G = try
            risch_integrate(g, x; build = build, lift = lift, verify = verify)
        catch e
            (e isa RischNotImplemented || e isa NotElementary) || rethrow()
            nothing
        finally
            CONST_SCALING[] = false
        end
        G === nothing && continue
        back = isone(σ) ? bd.x : mk(bd, :/, bd.x, cterm(bd, σ))
        bk(t) = isnode(t) ? term_rebuild(bd, t, Any[bk(a) for a in arguments(t)]) : (string(t) == xk ? back : t)
        r = subst_answer(G, bk, bd)
        r === nothing || return r
    end
    nothing
end

# f(σy)·σ in the normal form (as a term in x standing for y), or nothing when a radicand is not κ·(over ℚ)
function const_scaled(f, xk::String, d::Int, σ::Q, bd::Builder)
    S = QS{d}
    atoms = Dict{String,Any}()                          # atom key ↦ term (x-dependent radicals, functions)
    consts = Set{String}()                              # keys of constant atoms (d^(1/4))
    P = Dict{Vector{Tuple{String,Int}},S}
    sconst(c) = P(Tuple{String,Int}[] => c)
    addp(a, b) = (r = copy(a); for (k, c) in b; r[k] = get(r, k, zero(S)) + c; end; filter!(kv -> !iszero(kv[2]), r); r)
    function mulp(a, b)
        r = P()
        for (k1, c1) in a, (k2, c2) in b
            m = Dict{String,Int}()
            for (s, e) in Iterators.flatten((k1, k2))
                m[s] = get(m, s, 0) + e
            end
            k = sort!([(s, e) for (s, e) in m if e != 0])
            r[k] = get(r, k, zero(S)) + c1 * c2
        end
        filter!(kv -> !iszero(kv[2]), r)
        r
    end
    atom(key, t) = (atoms[key] = t; P([(key, 1)] => one(S)))
    qsqrt(c::Q) = (c > 0 && (sp = sqfree_split(numerator(c) * denominator(c)); sp[2] == 1 || sp[2] == d)) ?
                  qs_sqrt(S(c, Q(0))) : nothing
    function norm(t)
        if !safe_iscall(t) || isempty(arguments(t))
            string(t) == xk && return P([(xk, 1)] => S(σ, Q(0)))
            c = leaf_rational(t)
            c === nothing && return nothing
            return sconst(S(Q(c), Q(0)))
        end
        n, args = opname(operation(t)), arguments(t)
        if n === :+
            r = P()
            for a in args
                p = norm(a)
                p === nothing && return nothing
                r = addp(r, p)
            end
            return r
        elseif n === :- && 1 <= length(args) <= 2
            ps = Any[norm(a) for a in args]
            any(isnothing, ps) && return nothing
            neg = mulp(ps[end], sconst(S(Q(-1), Q(0))))
            return length(ps) == 1 ? neg : addp(ps[1], neg)
        elseif n === :*
            r = sconst(one(S))
            for a in args
                p = norm(a)
                p === nothing && return nothing
                r = mulp(r, p)
            end
            return r
        elseif n === :/ && length(args) == 2
            a, b = norm(args[1]), norm(args[2])
            (a === nothing || b === nothing || length(b) != 1) && return nothing
            (k, c), = b                                 # a monomial: its inverse
            return mulp(a, P([(s, -e) for (s, e) in k] => inv(c)))
        end
        rp = radical_parts(t)
        if rp !== nothing
            e, u = rp
            denominator(2 * e) == 1 || return nothing   # square roots only
            p = Int(numerator(2 * e))
            if !has_leaf(u, xk)
                c = leaf_rational(u)
                c === nothing && return nothing
                s = qsqrt(Q(c))
                s === nothing && return nothing
                return sconst(p >= 0 ? s^p : inv(s)^(-p))
            end
            U = norm(u)
            (U === nothing || isempty(U)) && return nothing
            any(k -> any(((s, _),) -> s in consts, k), keys(U)) && return nothing
            # U = κ U₀, U₀ over ℚ with integer coprime coefficients, κ > 0
            ks = sort!(collect(keys(U)))
            κ0 = U[ks[1]]
            U0 = Dict(k => c / κ0 for (k, c) in U)
            all(c -> iszero(c.b), values(U0)) || return nothing
            qs = [c.a for c in values(U0)]
            g = Q(reduce(gcd, numerator.(qs)), reduce(lcm, denominator.(qs)))
            (Float64(κ0.a) + Float64(κ0.b) * sqrt(d)) < 0 && (g = -g)
            κ = κ0 * S(g, Q(0))
            U0 = Dict(k => S(c.a / g, Q(0)) for (k, c) in U0)
            # √κ: in ℚ(√d), or √b·d^(1/4) for κ = b√d; a rational κ = s²m (m ≠ 1, d) keeps m inside
            sκ = qs_sqrt(κ)
            extra = nothing
            if sκ === nothing
                if iszero(κ.a) && κ.b > 0 && (sb = qsqrt(κ.b)) !== nothing
                    sκ = sb
                    key = "$(d)^(1/4)"
                    push!(consts, key)
                    extra = atom(key, mk(bd, :^, bd.lift(d), bd.lift(Q(1) // 4)))
                elseif iszero(κ.b)
                    m = sqfree_split(numerator(κ.a) * denominator(κ.a))[2]
                    sκ = qs_sqrt(κ * S(Q(1) // Q(m), Q(0)))
                    sκ === nothing && return nothing
                    U0 = Dict(k => c * S(Q(m), Q(0)) for (k, c) in U0)
                else
                    return nothing
                end
            end
            U0t = to_term(U0)
            rt = mk(bd, :sqrt, U0t)
            key = string(rt)
            atoms[key] = rt
            r = mulp(sconst(sκ), P([(key, 1)] => one(S)))
            extra === nothing || (r = mulp(r, extra))
            if p >= 0
                out = sconst(one(S))
                for _ in 1:p
                    out = mulp(out, r)
                end
                return out
            end
            length(r) == 1 || return nothing
            (k, c), = r
            return P([(s, e * p) for (s, e) in k] => inv(c)^(-p))
        end
        if n === :^ && length(args) == 2
            k = leaf_rational(args[2])
            (k === nothing || !isone(denominator(k))) && return nothing
            b = norm(args[1])
            b === nothing && return nothing
            k = Int(numerator(k))
            if k < 0
                length(b) == 1 || return nothing
                (kk, c), = b
                return P([(s, e * k) for (s, e) in kk] => inv(c)^(-k))
            end
            out = sconst(one(S))
            for _ in 1:k
                out = mulp(out, b)
            end
            return out
        end
        has_leaf(t, xk) || return nothing               # (other constants: not handled)
        ps = Any[norm(a) for a in args]
        any(isnothing, ps) && return nothing
        ft = term_rebuild(bd, t, Any[to_term(p) for p in ps])
        atom(string(ft), ft)
    end
    function to_term(p)
        isempty(p) && return bd.lift(0)
        ts = Any[]
        for k in sort!(collect(keys(p)))
            c = p[k]
            fs = Any[]
            for (s, e) in k
                a = s == xk ? bd.x : atoms[s]
                push!(fs, e == 1 ? a : mk(bd, :^, a, bd.lift(e)))
            end
            isone(c) || pushfirst!(fs, cterm(bd, c))     # one flat product (step IT sees d^(1/4))
            push!(ts, isempty(fs) ? cterm(bd, c) : length(fs) == 1 ? fs[1] : mk(bd, :*, fs...))
        end
        length(ts) == 1 ? ts[1] : mk(bd, :+, ts...)
    end
    F = norm(f)
    F === nothing && return nothing
    to_term(mulp(F, sconst(S(σ, Q(0)))))
end
