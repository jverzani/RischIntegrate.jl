# ---------------------------------------------------------------------------
# Special functions for term types that cannot hold them (SymEngine, Giac, … have no expinti(::T), li2(::T)):
# when building the answer fails with such a MethodError, the integrand is converted to an Expr and
# integrated again; the additive terms of the answer with special functions become `ExprTerm`s, evaluated
# numerically in an `IntegralWithRootSums` (as the ₂F₁ and Γ terms), and the other terms are rebuilt in the
# user's term type.
# ---------------------------------------------------------------------------
const SPECIAL_FNS = (expinti, sinint, cosint, sinhint, coshint, erf, erfi, li2, gamma)
const SPECIAL_NAMES = (:expinti, :sinint, :cosint, :sinhint, :coshint, :erf, :erfi, :li2, :gamma, :Ei, :Si, :Ci,
                       :_₁F₁, :pFq)

"""
    ExprTerm

A term of an antiderivative kept as an `Expr` (it has a special function the user's term type has no method
for), evaluated numerically through the `IntegralWithRootSums` it belongs to.
"""
struct ExprTerm
    ex::Any
    var::String
end
Base.show(io::IO, t::ExprTerm) = print(io, t.ex)
# real arithmetic first (expinti, li2, … have no complex methods), complex if that fails (log of a negative)
function expr_value(ex, xk::String, a)
    function ev(e)
        e isa Symbol && return string(e) == xk ? float(real(a)) : e === :ℯ ? float(ℯ) : e in (:π, :pi) ? float(π) :
                               throw(RischError("cannot evaluate the leaf $e numerically"))
        e isa Number && return float(e)
        f = op_function(e)
        f(map(ev, e.args[2:end])...)
    end
    try
        ComplexF64(ev(ex))
    catch err
        err isa RischError && rethrow()
        term_value(ex, xk, a)
    end
end
rs_value(t::ExprTerm, xk::String, a) = expr_value(t.ex, t.var, a)
rs_value_continuous(t::ExprTerm, xk::String, a::Real) = expr_value(t.ex, t.var, a)
depends_on(t::ExprTerm, yk::String) = has_x(t.ex, yk)

# a term as an Expr (operation names, leaves as Symbols or numbers)
function term_to_expr(t)
    if safe_iscall(t)
        args = arguments(t)
        isempty(args) || return Expr(:call, opname(operation(t)), (term_to_expr(a) for a in args)...)
    end
    r = leaf_rational(t)
    r !== nothing && return isone(denominator(r)) ? numerator(r) : r
    is_e_const(t) && return :ℯ
    Symbol(string(t))
end

has_special(ex) = ex isa Expr && ex.head === :call && (ex.args[1] in SPECIAL_NAMES || any(has_special, ex.args[2:end]))

# ∫ f dx through Expr, when f's term type has no method for a special function of the answer
function integrate_special_fallback(f, x; build = nothing, lift = nothing, verify::Bool = true)
    xk = string(x)
    leaves = Dict{String,Any}()                         # the user's leaves (x, parameters) by name
    collect_leaves!(leaves, f)
    ebuild(op, args...) = Expr(:call, nameof(op), args...)
    F = risch_integrate(term_to_expr(f), Symbol(xk); build = ebuild, lift = identity, verify = verify)
    E, rss = F isa IntegralWithRootSums ? (F.elementary, Any[F.rootsums...]) : (F, Any[])
    b0 = Builder(build === nothing ? auto_build(f, x) : build, lift === nothing ? auto_lift(f, x) : lift, x)
    function back(ex)                                   # Expr → the user's term type
        ex isa Symbol && return haskey(leaves, string(ex)) ? leaves[string(ex)] : ex === :ℯ ? mk(b0, :exp, b0.lift(1)) : ex
        ex isa Number && return b0.lift(ex)
        ex isa Expr && ex.head === :call || return ex
        b0.build(op_function(ex), (back(a) for a in ex.args[2:end])...)
    end
    summands = (E isa Expr && E.head === :call && E.args[1] === :+) ? E.args[2:end] : Any[E]
    elem = Any[]
    for s in summands
        has_special(s) ? push!(rss, ExprTerm(s, xk)) : push!(elem, back(s))
    end
    Et = isempty(elem) ? b0.lift(0) : length(elem) == 1 ? elem[1] : mk(b0, :+, elem...)
    IntegralWithRootSums(Et, rss, xk)
end

function collect_leaves!(d, t)
    if safe_iscall(t) && !isempty(arguments(t))
        foreach(a -> collect_leaves!(d, a), arguments(t))
    elseif leaf_rational(t) === nothing
        d[string(t)] = t
    end
    d
end
