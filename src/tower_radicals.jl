# ---------------------------------------------------------------------------
# Step RY: one radical y = P^(1/n) with P in an exponential/logarithmic tower K (not in ℚ(x); Rubi 218).
# f is written f = Σ_r A_r yʳ (0 ≤ r < n, A_r ∈ K) by term algebra (sums, products, integer powers, division by
# a monomial a·yᵏ, yⁿ = P). For r > 0 the ansatz ∫ A_r yʳ = B_r yʳ, B_r ∈ K, is the Risch differential equation
#   B_r' + (r/n)(P'/P) B_r = A_r                            ((B yʳ)' = (B' + (r/n) B P'/P) yʳ)
# solved in K (`rde`); A₀ is integrated as usual. No solution for some r: nothing (no logarithmic part in y).
# ---------------------------------------------------------------------------
const TOWER_RADICAL = Ref(false)                        # no nested uses

function try_tower_radical(f, x; build = nothing, lift = nothing, verify::Bool = true)
    @nospecialize f x
    TOWER_RADICAL[] && return nothing
    xk = string(x)
    rads = [(e, u) for (e, u) in collect_radicals(f, xk) if depends_on(u, xk)]
    (isempty(rads) || length(unique(string(u) for (_, u) in rads)) != 1) && return nothing
    Pt = rads[1][2]
    Ps = string(Pt)
    (isempty(collect_radicals(Pt, xk)) && radicand_element(Pt, xk) === nothing) || return nothing
    n = lcm([Int(denominator(e)) for (e, _) in rads])
    bd = Builder(build === nothing ? auto_build(f, x) : build, lift === nothing ? auto_lift(f, x) : lift, x)
    # f as Dict(k => coefficient term), f = Σ cₖ yᵏ (k ∈ ℤ), or nothing
    one_t = bd.lift(1)
    addto!(d, k, c) = (d[k] = haskey(d, k) ? mk(bd, :+, d[k], c) : c; d)
    function mul(a, b)
        d = Dict{Int,Any}()
        for (i, c) in a, (j, e) in b
            addto!(d, i + j, mk(bd, :*, c, e))
        end
        d
    end
    function dec(t)
        occursin(Ps, string(t)) || return Dict{Int,Any}(0 => t)
        rp = radical_parts(t)
        if rp !== nothing && string(rp[2]) == Ps
            k = rp[1] * n
            isone(denominator(k)) || return nothing
            return Dict{Int,Any}(Int(numerator(k)) => one_t)
        end
        safe_iscall(t) || return nothing
        op, args = opname(operation(t)), arguments(t)
        ds = Any[dec(a) for a in args]
        any(isnothing, ds) && return nothing
        if op === :+
            d = Dict{Int,Any}()
            foreach(di -> foreach(((k, c),) -> addto!(d, k, c), di), ds)
            return d
        elseif op === :- && length(ds) == 1
            return Dict{Int,Any}(k => mk(bd, :*, bd.lift(-1), c) for (k, c) in ds[1])
        elseif op === :- && length(ds) == 2
            d = copy(ds[1])
            foreach(((k, c),) -> addto!(d, k, mk(bd, :*, bd.lift(-1), c)), ds[2])
            return d
        elseif op === :*
            return reduce(mul, ds)
        elseif op === :/ && length(ds) == 2
            length(ds[2]) == 1 || return nothing             # only monomial denominators a·yᵏ
            (k, c), = ds[2]
            return Dict{Int,Any}(j - k => mk(bd, :/, e, c) for (j, e) in ds[1])
        elseif op === :^ && length(ds) == 2 && length(ds[2]) == 1 && haskey(ds[2], 0)
            p = leaf_rational(args[2])
            (p === nothing || !isone(denominator(p))) && return nothing
            p = Int(numerator(p))
            if length(ds[1]) == 1
                (k, c), = ds[1]
                return Dict{Int,Any}(k * p => mk(bd, :^, c, bd.lift(p)))
            end
            (1 <= p <= 4) || return nothing
            return reduce(mul, fill(ds[1], p))
        end
        nothing
    end
    d = dec(f)
    (d === nothing || all(k -> mod(k, n) == 0, keys(d))) && return nothing
    # yᵏ = P^q yʳ, k = q n + r
    A = Dict{Int,Any}()
    for (k, c) in d
        q, r = fldmod(k, n)
        addto!(A, r, q == 0 ? c : mk(bd, :*, c, mk(bd, :^, Pt, bd.lift(q))))
    end
    T, Pel, Aels = try
        T, _ = build_tower(mk(bd, :+, Pt, values(A)...), xk; minimize = false)
        T, parse_tower(Pt, T), Dict(r => parse_tower(c, T) for (r, c) in A)
    catch err
        (err isa RischNotImplemented || err isa RischError || err isa NeedComplex) || rethrow()
        return nothing
    end
    m = length(T.levels)
    m >= 1 || return nothing
    is_complex_field(ctype(T)) && return nothing        # (no real forms here: trig towers over ℚ(i))
    lift_m(e) = liftto(T, e, m)
    Pm = lift_m(Pel)
    dlogP = D(T, m, Pm) / Pm
    bc = Builder(bd.build, bd.lift, bd.x, T.consts)
    parts = Any[]
    for r in sort!(collect(keys(Aels)))
        r == 0 && continue
        g = lift_m(Aels[r])
        iszero(g) && continue
        fr = dlogP * lconst(T, cfromQ(ctype(T), Q(r) // n), m)
        B = try
            rde(T, m, fr, g)
        catch err
            (err isa RischNotImplemented || err isa RischError || err isa NotElementary) || rethrow()
            nothing
        end
        B === nothing && return nothing
        D(T, m, B) + fr * B == g || throw(RischError("internal check failed: step RY"))
        yr = mk(bc, :^, Pt, bc.lift(Q(r) // n))
        push!(parts, mk(bc, :*, tower_to_term(bc, T, B), yr))
    end
    if haskey(A, 0)
        TOWER_RADICAL[] = true
        G = try
            risch_integrate(A[0], x; build = build, lift = lift, verify = verify)
        catch err
            (err isa RischNotImplemented || err isa NotElementary) || rethrow()
            nothing
        finally
            TOWER_RADICAL[] = false
        end
        G === nothing && return nothing
        push!(parts, G)
    end
    add_answers(bd, parts, xk)
end
