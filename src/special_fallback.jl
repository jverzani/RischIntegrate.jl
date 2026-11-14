# ---------------------------------------------------------------------------
# Special functions for term types that cannot hold them (SymEngine, Giac, … have no expinti(::T), li2(::T)):
# when building the answer fails with such a MethodError, the integrand is converted to an Expr and
# integrated again; the additive terms of the answer with special functions become `ExprTerm`s, evaluated
# numerically in an `IntegralWithRootSums` (as the ₂F₁ and Γ terms), and the other terms are rebuilt in the
# user's term type.
# ---------------------------------------------------------------------------
const SPECIAL_FNS = (expinti, sinint, cosint, sinhint, coshint, erf, erfi, li2, gamma, clausen2, clausen, repolylog, impolylog, _₂F₁, rehyp2f1, imhyp2f1)
const SPECIAL_NAMES = (:expinti, :sinint, :cosint, :sinhint, :coshint, :erf, :erfi, :li2, :gamma, :Ei, :Si, :Ci,
                       :_₁F₁, :_₂F₁, :pFq, :clausen2, :clausen, :repolylog, :impolylog, :rehyp2f1, :imhyp2f1)

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
    @nospecialize f x
    xk = string(x)
    leaves = Dict{String,Any}()                         # the user's leaves (x, parameters) by name
    collect_leaves!(leaves, f)
    F = risch_integrate(term_to_expr(f), Symbol(xk); build = expr_build, lift = identity, verify = verify)
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

# Step IP: ∫ f dx for a radical whose radicand has the imaginary unit (√(x² - i), SymPy #25314), which the radical
# steps (over ℚ(x)) refuse: i is taken as a parameter ⅈ (through Expr, as above), the radicand is then one with a
# symbolic constant (step PR: x = √ⅈ u), and ⅈ = i is put back. The answer, for generic values of ⅈ, is checked
# numerically at ⅈ = i (the branches of √ⅈ are those of the principal square root). Nothing when it fails, has a
# RootSum, or i appears outside the user's leaves in a way Expr cannot hold.
const IMAG_PARAM_NAME = "ⅈ"
function integrate_imag_param(f, x; build = nothing, lift = nothing, verify::Bool = true)
    @nospecialize f x
    IMAG_PARAM[] && return nothing
    xk = string(x)
    # (i only outside the radicals, (a + i a tan(c + d x))⁴ beside sec^(13/2): the second integration finds nothing
    # the first did not, and took up to 4 minutes)
    any(((_, u),) -> has_imag_unit(u), collect_radicals(f, xk)) || return nothing
    leaves = Dict{String,Any}()
    collect_leaves!(leaves, f)
    haskey(leaves, IMAG_PARAM_NAME) && return nothing
    ii = Symbol(IMAG_PARAM_NAME)
    toexpr(t) = is_imag_unit(t) ? ii : safe_iscall(t) && !isempty(arguments(t)) ?
        Expr(:call, opname(operation(t)), (toexpr(a) for a in arguments(t))...) : term_to_expr(t)
    IMAG_PARAM[] = true
    F = try
        risch_integrate(toexpr(f), Symbol(xk); build = expr_build, lift = identity, verify = verify)
    catch e
        (e isa RischNotImplemented || e isa NotElementary) || rethrow()
        nothing
    finally
        IMAG_PARAM[] = false
    end
    (F === nothing || F isa IntegralWithRootSums || has_special(F)) && return nothing
    b0 = Builder(build === nothing ? auto_build(f, x) : build, lift === nothing ? auto_lift(f, x) : lift, x)
    function back(ex)                                   # Expr → the user's term type, ⅈ ↦ i
        ex === ii && return b0.lift(im)
        ex isa Symbol && return haskey(leaves, string(ex)) ? leaves[string(ex)] : ex === :ℯ ? mk(b0, :exp, b0.lift(1)) : ex
        ex isa Number && return b0.lift(ex)
        ex isa Expr && ex.head === :call || return ex
        b0.build(op_function(ex), (back(a) for a in ex.args[2:end])...)
    end
    G = back(F)
    (verify && !numeric_antiderivative(f, G, xk)) && return nothing
    G
end
