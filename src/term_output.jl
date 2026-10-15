# ---------------------------------------------------------------------------
# Output: build a term from the exact result, by *calling operations as functions*
# ---------------------------------------------------------------------------
fitint(n::BigInt) = typemin(Int) <= n <= typemax(Int) ? Int(n) : n
function num(c::Q)
    n, d = numerator(c), denominator(c)
    isone(d) && return fitint(n)
    (typemin(Int) <= n <= typemax(Int) && d <= typemax(Int)) ? Int(n) // Int(d) : c
end

# A generator tⱼ of a transcendental constant field ℚ(t₁, …, tₖ) (Step 6): tⱼ = exp(arg) or
# log(arg), arg ∈ ℚ. The field type only knows "k indeterminates"; what they stand for is
# this list, kept by the tower (`T.consts`) and by the Builder (for output).
struct ConstGen
    kind::Symbol          # :exp, :log, :expi, or :sym (a symbolic parameter, step SY)
    arg::Q
    term::Any             # :sym: the user's symbol (printed back as itself), else nothing
end
ConstGen(kind::Symbol, arg::Q) = ConstGen(kind, arg, nothing)
symname(g::ConstGen) = g.kind === :sym ? string(g.term) : ""
Base.:(==)(a::ConstGen, b::ConstGen) = a.kind === b.kind && a.arg == b.arg && symname(a) == symname(b)
Base.hash(g::ConstGen, h::UInt) = hash(symname(g), hash(g.arg, hash(g.kind, h)))

struct Builder
    build::Any
    lift::Any
    x::Any
    consts::Vector{ConstGen}  # meaning of the indeterminates of the constant field (output)
end
Builder(build, lift, x) = Builder(build, lift, x, ConstGen[])
const OPS = Dict{Symbol,Function}(:+ => +, :* => *, :/ => /, :^ => ^, :exp => exp,
                                  :log => log, :atan => atan, :sqrt => sqrt,
                                  :sin => sin, :cos => cos, :tan => tan, :cot => cot, :sec => sec, :csc => csc,
                                  :asin => asin, :acos => acos, :acot => acot, :acsc => acsc, :asec => asec,
                                  # SpecialFunctions (Step 8a): Ei, Si, Ci, erf, erfi
                                  :Ei => expinti, :Si => sinint, :Ci => cosint, :erf => erf, :erfi => erfi,
                                  # PolyLog (step DL): the dilogarithm Li₂
                                  :li2 => li2)
mk(b::Builder, name::Symbol, args...) = b.build(OPS[name], args...)
# the function of a term's operation; the operation of an Expr is a Symbol: the function of OPS or
# of Base with that name (expinti, sinh, …), else the Symbol itself
function op_function(t)
    op = operation(t)
    n = opname(op)
    haskey(OPS, n) && return OPS[n]
    n === :- && return (-)
    op isa Symbol || return op
    for f in values(OPS)
        nameof(f) === n && return f
    end
    isdefined(Base, n) && (f = getfield(Base, n)) isa Function ? f : op
end

# a constant of the differential field as a term (part of the constant-field interface;
# only C = ℚ is implemented: rationals are lifted into the package's number type)
cterm(b::Builder, c::Q) = b.lift(num(c))
function cterm(b::Builder, c::QS{d}) where {d}         # a + b√d, with sqrt(d) kept symbolic
    iszero(c.b) && return cterm(b, c.a)
    r = mk(b, :sqrt, b.lift(d))
    s = isone(c.b) ? r : mk(b, :*, cterm(b, c.b), r)
    iszero(c.a) ? s : mk(b, :+, cterm(b, c.a), s)
end
cterm(b::Builder, c) = throw(RischNotImplemented(
    "output of constants of type $(typeof(c)) is not implemented"))

# constants of ℚ(i) and ℚ(i)(√d) in real-form output: they must be real (Step 7)
function cterm(b::Builder, c::QI)
    iszero(c.im) || throw(RischError("a non-real constant $c reached the real-form output"))
    cterm(b, c.re)
end
function cterm(b::Builder, c::QSB{d,QI}) where {d}
    (iszero(c.a.im) && iszero(c.b.im)) || throw(RischError("a non-real constant $c reached the real-form output"))
    cterm(b, QS{d}(c.a.re, c.b.re))
end

# c ∈ ℚ(t₁, …, tₖ) = B(tₖ): a rational function of tₖ with coefficients in B, tₖ from b.consts
function cterm(b::Builder, c::Frac{<:UPoly})
    k = cdepth(typeof(c))
    k <= length(b.consts) || throw(RischError(
        "constant field with $k generators but only $(length(b.consts)) are described"))
    b.consts[k].kind === :expi && return cterm_expi(b, c, b.consts[k].arg)
    t = constgen_term(b, b.consts[k])
    n = cpoly_term(b, c.num, t)
    isone(c.den) ? n : mk(b, :/, n, cpoly_term(b, c.den, t))
end
# a real (σ-invariant) constant c ∈ B(τ), τ = e^(i·a): c = (N·σD)/(D·σD) with σ-invariant Laurent
# polynomials in τ, written with cos(k·a) and sin(k·a) (as for a :trig level of a tower)
function cterm_expi(b::Builder, c::Frac{<:UPoly}, a::Q)
    B = eltype(c.num.c)
    sD = Dict{Int,B}(-(j - 1) => cconj_g(b.consts, d) for (j, d) in enumerate(c.den.c) if !iszero(d))
    A = laurent_mul(laurent_of(c.num), sD)
    Bd = laurent_mul(laurent_of(c.den), sD)
    n = cterm_laurent(b, A, a, B)
    if length(Bd) == 1 && haskey(Bd, 0)
        return isone(Bd[0]) ? n : mk(b, :/, n, cterm(b, Bd[0]))
    end
    mk(b, :/, n, cterm_laurent(b, Bd, a, B))
end
function cterm_laurent(b::Builder, L::Dict, a::Q, ::Type{B}) where {B}
    all(k -> haskey(L, -k), keys(L)) || throw(RischError("a constant in the real-form output is not real"))
    I = cimag(B)
    ts = Any[]
    c0 = get(L, 0, zero(B))
    iszero(c0) || push!(ts, cterm(b, c0))
    for k in sort([k for k in keys(L) if k > 0])
        ck, cm = L[k], L[-k]
        ka = cterm(b, k * a)
        for (coef, fn) in ((ck + cm, :cos), (I * (ck - cm), :sin))
            iszero(coef) && continue
            tr = mk(b, fn, ka)
            push!(ts, isone(coef) ? tr : mk(b, :*, cterm(b, coef), tr))
        end
    end
    isempty(ts) && return b.lift(0)
    length(ts) == 1 ? ts[1] : mk(b, :+, ts...)
end

constgen_term(b::Builder, g::ConstGen) =
    g.kind === :exp ? mk(b, :exp, cterm(b, g.arg)) :
    g.kind === :log ? mk(b, :log, cterm(b, g.arg)) :
    g.kind === :sym ? g.term :
    throw(RischError("unknown constant generator kind $(g.kind)"))
function cpoly_term(b::Builder, p::UPoly, t)
    iszero(p) && return b.lift(0)
    ts = Any[]
    for (i, c) in enumerate(p.c)
        iszero(c) && continue
        k = i - 1
        if k == 0
            push!(ts, cterm(b, c))
        else
            tk = k == 1 ? t : mk(b, :^, t, b.lift(k))
            push!(ts, isone(c) ? tk : mk(b, :*, cterm(b, c), tk))
        end
    end
    length(ts) == 1 ? ts[1] : mk(b, :+, ts...)
end

default_build(op, args...) = op(args...)

# Constants such as sqrt(3) must stay symbolic. SimpleExpressions-like types defer
# evaluation only when a symbolic variable is involved, so a constant-only call
# `op(args...)` is built by substituting into `op(x, args[2:end]...)` (the
# documented `u(value, :)` substitution); other types simply apply the operation.
function placeholder_call(x, op, args)
    isempty(args) && return nothing
    try
        u = op(x, args[2:end]...)
        u isa Function || return nothing
        r = u(args[1], :)
        r isa Function ? r : nothing
    catch
        nothing
    end
end
function deferred_call(x, op, args)
    r = placeholder_call(x, op, args)
    r === nothing ? op(args...) : r
end
function auto_build(f, x)
    typeof(x) <: Function || return x isa Number ? default_build : (op, args...) -> exact_call(x, op, args)
    (op, args...) -> any(a -> a isa Function, args) ? op(args...) : deferred_call(x, op, args)
end

# Other term types (SymbolicUtils): a call of sqrt, cbrt, log or exp on numbers only is built with
# TermInterface's `maketerm` for the type of the variable, which keeps it unevaluated (sqrt(2), not
# 1.414…); an integer value (sqrt(1), log(1)) is returned as an integer. An operation without a
# method for the arguments (PolyLog.li2 of a term) is built with `maketerm` too. If the type does
# not build such a term, the operation is applied to the numbers as terms, a * one(x) (Giac.jl,
# whose `maketerm` evaluates sqrt(2) to a float), else to the numbers (or its MethodError raised).
const EXACT_OPS = (sqrt, cbrt, log, exp)
function exact_call(x, op, args)
    T = typeof(x)
    make() = (r = try maketerm(T, op, Any[args...], nothing) catch; nothing end; r isa T ? r : nothing)
    lifted() = (r = try op((a * one(x) for a in args)...) catch; nothing end; r isa T ? r : nothing)
    if op in EXACT_OPS && all(a -> a isa Number, args)
        v = op(args...)
        v isa AbstractFloat && isinteger(v) && abs(v) < 2^53 && return Int(v)
        r = make()
        r === nothing && (r = lifted())
        return r === nothing ? v : r
    end
    try
        op(args...)
    catch e
        e isa MethodError || rethrow()
        r = make()
        r === nothing ? rethrow() : r
    end
end

function auto_lift(f, x)
    for t in (f, x)
        if t isa Number && !(t isa Real)
            T = typeof(t)
            return v -> try
                T(v)
            catch
                v
            end
        end
    end
    identity
end

function poly_term(b::Builder, p::UPoly)
    iszero(p) && return b.lift(0)
    ts = Any[]
    for (i, c) in enumerate(p.c)
        iszero(c) && continue
        k = i - 1
        if k == 0
            push!(ts, cterm(b, c))
        else
            xk = k == 1 ? b.x : mk(b, :^, b.x, b.lift(k))
            push!(ts, isone(c) ? xk : mk(b, :*, cterm(b, c), xk))
        end
    end
    length(ts) == 1 ? ts[1] : mk(b, :+, ts...)
end
frac_term(b::Builder, f::Frac{<:UPoly}) =
    isone(f.den) ? poly_term(b, f.num) : mk(b, :/, poly_term(b, f.num), poly_term(b, f.den))

# a log argument as a term; a monic perfect square v² (the real form log|v| = log(v²)/2, step RL)
# is printed as v^2
function log_arg_term(b::Builder, w::UPoly)
    if degree(w) >= 2 && isone(lc(w))
        sf = squarefree(w)
        if !isempty(sf) && all(iseven(k) for (_, k) in sf)
            v = prod(p^(k ÷ 2) for (p, k) in sf)
            return mk(b, :^, poly_term(b, v), b.lift(2))
        end
    end
    poly_term(b, w)
end
log_arg_term(b::Builder, f::Frac) =
    isone(f.den) ? log_arg_term(b, f.num) : mk(b, :/, log_arg_term(b, f.num), log_arg_term(b, f.den))

function to_term(b::Builder, res::RationalIntegral)
    ts = Any[]
    iszero(res.rational) || push!(ts, frac_term(b, res.rational))
    for (c, w) in res.logs
        l = mk(b, :log, log_arg_term(b, w))
        push!(ts, isone(c) ? l : mk(b, :*, cterm(b, c), l))
    end
    for (c, u) in res.atans
        l = mk(b, :atan, frac_term(b, u))
        push!(ts, isone(c) ? l : mk(b, :*, cterm(b, c), l))
    end
    for q in res.quads
        if q isa RationalIntegral || q isa QuarticNested
            push!(ts, to_term(b, q))
        elseif q isa QuadLog
            r = mk(b, :sqrt, b.lift(q.d))
            top = mk(b, :+, poly_term(b, q.U), mk(b, :*, r, poly_term(b, q.V)))
            bot = mk(b, :+, poly_term(b, q.U), mk(b, :*, b.lift(-1), r, poly_term(b, q.V)))
            ratio = mk(b, :/, top, bot)
            l = mk(b, :log, q.sq ? mk(b, :^, ratio, b.lift(2)) : ratio)
            β = q.sq ? q.β / 2 : q.β
            push!(ts, isone(β) ? mk(b, :*, r, l) : mk(b, :*, cterm(b, β), r, l))
        else
            r = mk(b, :sqrt, b.lift(q.e))
            arg = q.inverted ? mk(b, :/, frac_term(b, q.u), r) : mk(b, :*, r, frac_term(b, q.u))
            l = mk(b, :atan, arg)
            push!(ts, isone(q.c) ? mk(b, :*, r, l) : mk(b, :*, b.lift(num(q.c)), r, l))
        end
    end
    isempty(ts) && return b.lift(0)
    length(ts) == 1 ? ts[1] : mk(b, :+, ts...)
end
