# ---------------------------------------------------------------------------
# TermInterface front end: term -> ℚ(x)
# ---------------------------------------------------------------------------
safe_iscall(t) = try iscall(t) === true catch; false end

# Numeric leaves of symbolic packages. Besides Julia numbers these include
#  * callable constants (SimpleExpressions represents the `-1` in `x^2 - 1` as a
#    function-like object): evaluated with `t()`, which fails for variables;
#  * `Basic` numbers (SymEngine) and anything else numeric: read from the exact
#    printed form.
function leaf_rational(t)
    t isa Integer && return Q(t)
    t isa Rational && return Q(t)
    t isa AbstractFloat && return isfinite(t) ? rationalize(BigInt, t) : nothing
    if t isa Function
        v = try
            t()
        catch
            nothing
        end
        v isa Real && return leaf_rational(v)
    end
    s = string(t)
    (startswith(s, "(") && endswith(s, ")")) && (s = s[nextind(s, 1):prevind(s, lastindex(s))])
    m = match(r"^(-?\d+)(?:/{1,2}(\d+))?$", s)          # 3, -1/2, and Symbolics' (1//3)
    if m !== nothing
        n = parse(BigInt, m.captures[1])
        d = m.captures[2] === nothing ? big(1) : parse(BigInt, m.captures[2])
        return Q(n // d)
    end
    occursin(r"^-?(\d+\.\d*|\.\d+|\d+)([eE][+-]?\d+)?$", s) ?
        rationalize(BigInt, parse(Float64, s)) : nothing
end

opname(op) = op isa Symbol ? op : (op isa Function ? nameof(op) : opname_other(op))
# other callable operations (e.g. SymEngine's SymFunction("li2")): their name when they have one
function opname_other(op)
    n = try
        nameof(op)
    catch
        nothing
    end
    n isa Symbol ? n : Symbol(string(op))
end

# the integer value of a constant rational function, or nothing
function const_int(f::CXF)
    (isone(f.den) && degree(f.num) <= 0) || return nothing
    c = isempty(f.num.c) ? Q(0) : f.num.c[1]
    isone(denominator(c)) ? Int(numerator(c)) : nothing
end

const NONRATIONAL = (:exp, :log, :sin, :cos, :tan, :cot, :sec, :csc, :atan, :sinh, :cosh, :tanh, :abs, :sqrt, :cbrt)

function parse_rational(t, xk::String)::CXF
    if safe_iscall(t)
        args = arguments(t)
        if !isempty(args)
            n = opname(operation(t))
            n in NONRATIONAL && throw(RischNotImplemented(
                "`$n` is not a rational function; integrands with exp/log towers " *
                "are planned for Stage 2/3 (see the roadmap in Risch.jl)"))
            a = CXF[parse_rational(u, xk) for u in args]
            if n === :+
                return foldl(+, a; init = zero(CXF))
            elseif n === :-
                return length(a) == 1 ? -a[1] : a[1] - foldl(+, a[2:end]; init = zero(CXF))
            elseif n === :*
                return foldl(*, a; init = one(CXF))
            elseif n === :/ && length(a) == 2
                return a[1] / a[2]
            elseif n === :inv && length(a) == 1
                return inv(a[1])
            elseif n === :^ && length(a) == 2
                k = const_int(a[2])
                (k === nothing || abs(k) > 10_000) &&
                    throw(RischNotImplemented("only small integer powers are rational functions"))
                return a[1]^k
            else
                throw(RischNotImplemented("unsupported operation `$n`"))
            end
        end
    end
    string(t) == xk && return frac(xpoly(Q))
    r = leaf_rational(t)
    r !== nothing && return kconst(r)
    throw(RischNotImplemented("symbol `$t` is not the integration variable; " *
                              "symbolic parameters are not supported yet"))
end
