# ---------------------------------------------------------------------------
# Step LS: ∫ Σ tᵢ = Σ ∫ tᵢ, tried when the whole integrand failed: the terms can need different routes
# (∫ 1/x + (1 + 1/x)/(x + log x)^(3/2): log x, then u = x + log x; Rubi 219). A quotient N/D with N a sum
# is split as Σ Nᵢ/D (Rubi 220). Terms with the same radicals stay together (the radical-free ones of Rubi 220
# sum to 1/x); each group is integrated as usual, and a group that fails gives up.
# Step EP: (bʷ)^r = b^(w r) for a positive constant base b (b ∈ ℚ, ℯ) or exp(w)^r = exp(w r), before the
# integrand is parsed ((3^(3x))^(1/4) = 3^(3x/4), Rubi 1533).
# ---------------------------------------------------------------------------
const SUM_SPLIT = Ref(0)                                # nesting (at most 2)

function additive_terms(bd::Builder, f)
    safe_iscall(f) || return Any[]
    n, args = opname(operation(f)), arguments(f)
    n === :+ && return Any[a for a in args]
    n === :- && length(args) == 2 && return Any[args[1], mk(bd, :*, bd.lift(-1), args[2])]
    if n === :/ && length(args) == 2
        ts = additive_terms(bd, args[1])
        return Any[mk(bd, :/, t, args[2]) for t in ts]
    end
    Any[]
end

function try_sum_split(f, x; build = nothing, lift = nothing, verify::Bool = true)
    @nospecialize f x
    SUM_SPLIT[] < 2 || return nothing
    xk = string(x)
    bd = Builder(build === nothing ? auto_build(f, x) : build, lift === nothing ? auto_lift(f, x) : lift, x)
    ts = additive_terms(bd, f)
    length(ts) >= 2 || return nothing
    # the terms grouped by the radicals they have (the radical-free ones together: in Rubi 220 only their sum
    # is elementary); single terms when there is one group
    groups = Dict{String,Vector{Any}}()
    for t in ts
        k = join(sort!([string(u) * "^" * string(e) for (e, u) in collect_radicals(t, xk)]), ",")
        push!(get!(groups, k, Any[]), t)
    end
    if length(groups) >= 2
        ts = Any[length(g) == 1 ? g[1] : mk(bd, :+, g...) for g in values(groups)]
    end
    SUM_SPLIT[] += 1
    Fs = try
        Any[risch_integrate(t, x; build = build, lift = lift, verify = verify) for t in ts]
    catch e
        (e isa RischNotImplemented || e isa NotElementary) || rethrow()
        nothing
    finally
        SUM_SPLIT[] -= 1
    end
    Fs === nothing && return nothing
    els = Any[F isa IntegralWithRootSums ? F.elementary : F for F in Fs]
    E = length(els) == 1 ? els[1] : mk(bd, :+, els...)
    any(F -> F isa IntegralWithRootSums, Fs) || return E
    IntegralWithRootSums(E, Any[rs for F in Fs if F isa IntegralWithRootSums for rs in F.rootsums], xk)
end

# f with (bʷ)^r written b^(w r) (see the header), or nothing if there is none
function merge_exp_powers(f, x, build, lift)
    @nospecialize f x
    xk = string(x)
    bd = Builder(build === nothing ? auto_build(f, x) : build, lift === nothing ? auto_lift(f, x) : lift, x)
    changed = false
    function walk(t)
        safe_iscall(t) || return t
        args = arguments(t)
        isempty(args) && return t
        rp = radical_parts(t)
        if rp !== nothing
            r, B = rp
            if safe_iscall(B) && depends_on(B, xk)
                bn, ba = opname(operation(B)), arguments(B)
                if bn === :exp && length(ba) == 1
                    changed = true
                    return mk(bd, :exp, mk(bd, :*, cterm(bd, r), walk(ba[1])))
                elseif bn === :^ && length(ba) == 2 && !depends_on(ba[1], xk) &&
                       (is_e_const(ba[1]) || (q = leaf_rational(ba[1]); q !== nothing && q > 0))
                    changed = true
                    return mk(bd, :^, ba[1], mk(bd, :*, cterm(bd, r), walk(ba[2])))
                end
            end
        end
        term_rebuild(bd, t, Any[walk(a) for a in args])
    end
    g = walk(f)
    changed ? g : nothing
end
