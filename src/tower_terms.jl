# --- term -> tower element ----------------------------------------------------
function unify(T::Tower, a, b)
    j = max(levelof(T, a), levelof(T, b))
    liftto(T, a, j), liftto(T, b, j)
end
function fold_op(T::Tower, op, els)
    acc = els[1]
    for e in els[2:end]
        a, b = unify(T, acc, e)
        acc = op(a, b)
    end
    acc
end

# The constant e, however the package prints it: Julia's ℯ, SymEngine's `E`, or
# `exp(1)` (SymEngine builds exp(u) as the power E^u).
is_e_const(t) = !safe_iscall(t) && string(t) in ("ℯ", "E", "exp(1)")

const ALGEBRAIC = (:sqrt, :cbrt)
const TRIG = (:sin, :cos, :tan, :cot, :sec, :csc, :atan, :abs)

function parse_tower(t, T::Tower)
    @nospecialize t
    if T.subst !== nothing                     # Step 10: x ↦ φ(t), radicals ↦ powers of t
        r = T.subst(t, T)
        r === nothing || return r
    end
    if safe_iscall(t)
        args = arguments(t)
        if !isempty(args)
            n = opname(operation(t))
            # step TS2: a trigonometric or hyperbolic function of a parameter term (cos a) is an opaque constant
            if n in SHIFT_TRIG && length(args) == 1 && !has_x(args[1], T.xk) && has_param(args[1], T.xk)
                return sym_const(T, t)
            end
            rp = radical_parts(t)                       # √(2h): an opaque constant (as cos a)
            (rp !== nothing && opaque_radical(rp[2], T.xk)) && return sym_const(T, t)
            if n in (:sin, :cos, :tan, :cot, :sec, :csc) && length(args) == 1   # Step 7: θ = exp(i·u) over ℚ(i)
                C = ctype(T)
                is_complex_field(C) || throw(NeedComplex())
                u = parse_tower(args[1], T)
                ci = cimag(C)
                E = make_exp(T, u * lconst(T, ci, levelof(T, u)))
                l = levelof(T, E)
                s2i = E - inv(E)                                 # 2i sin u
                c2 = E + inv(E)                                  # 2 cos u
                n === :sin && return s2i * lconst(T, inv(ci + ci), l)
                n === :cos && return c2 * lconst(T, inv(cfromQ(C, Q(2))), l)
                n === :tan && return s2i / (c2 * lconst(T, ci, l))   # tan = sin/cos
                n === :cot && return c2 * lconst(T, ci, l) / s2i     # cot = cos/sin
                n === :sec && return lconst(T, cfromQ(C, Q(2)), l) / c2       # sec = 1/cos
                return lconst(T, ci + ci, l) / s2i                            # csc = 1/sin
            end
            if n === :atan && length(args) == 1                  # step TA
                return make_atan(T, parse_tower(args[1], T))
            end
            n in TRIG && throw(RischNotImplemented(
                "`$n` is not supported: only sin, cos, tan, cot, sec and csc of tower elements are"))
            n in ALGEBRAIC && throw(RischNotImplemented(
                "`$n` is an algebraic (radical) function; only transcendental towers are supported"))
            if n === :^ && length(args) == 2 && is_e_const(args[1])
                return make_exp(T, parse_tower(args[2], T))          # E^u = exp(u)
            end
            a = Any[parse_tower(u, T) for u in args]
            if n === :+
                return fold_op(T, +, a)
            elseif n === :-
                length(a) == 1 && return -a[1]
                rest = fold_op(T, +, a[2:end])
                x1, b1 = unify(T, a[1], rest)
                return x1 - b1
            elseif n === :*
                return fold_op(T, *, a)
            elseif n === :/ && length(a) == 2
                x1, b1 = unify(T, a[1], a[2])
                return x1 / b1
            elseif n === :inv && length(a) == 1
                return inv(a[1])
            elseif n === :exp && length(a) == 1
                return make_exp(T, a[1])
            elseif n === :log && length(a) == 1
                return make_log(T, a[1])
            elseif n in (:sinh, :cosh, :tanh, :coth, :sech, :csch) && length(a) == 1
                e1 = make_exp(T, a[1])
                e2 = make_exp(T, -a[1])
                p, m = unify(T, e1, e2)
                half = lq(T, Q(1) // 2, levelof(T, p))
                s = (p - m) * half
                c = (p + m) * half
                n === :sinh && return s
                n === :cosh && return c
                n === :tanh && return s / c
                n === :coth && return c / s
                n === :sech && return inv(c)
                return inv(s)                                   # csch
            elseif n === :^ && length(a) == 2
                base, ex = a
                k = const_value(T, ex)
                if k !== nothing
                    kq = crational(k)
                    if kq !== nothing
                        isone(denominator(kq)) && abs(kq) <= 10_000 && return base^Int(numerator(kq))
                        throw(RischNotImplemented("rational power $kq is an algebraic (radical) function"))
                    end
                    # a non-rational constant exponent (a parameter, e, …): u^k = exp(k log u) (SY)
                end
                lg = make_log(T, base)
                p, m = unify(T, ex, lg)
                return make_exp(T, p * m)
            else
                throw(RischNotImplemented("unsupported operation `$n`"))
            end
        end
    end
    string(t) == T.xk && return frac(xpoly(ctype(T)))
    is_e_const(t) && return lconst(T, const_exp(T, one(ctype(T))), 0)
    r = leaf_rational(t)
    r !== nothing && return lq(T, r, 0)
    # step SY: any other symbol is a parameter, a new indeterminate of the constant field
    # ℚ(…, a) (answers hold for generic values of a)
    check_leaf(t, T.xk)
    sym_const(T, t)
end

# step WR: a leaf that prints with the variable in it is an expression the TermInterface methods do
# not open (e.g. a Symbolics `Num` wrapper: `iscall` is false). As a parameter it would give
# ∫ f dx = f·x, "verified" since f would be a constant; refuse it instead.
mentions_var(s::String, xk::String) = occursin(Regex("(*UCP)(?<!\\w)\\Q" * xk * "\\E(?!\\w)"), s)
function check_leaf(t, xk::String)
    s = string(t)
    (s != xk && mentions_var(s, xk)) && throw(RischNotImplemented(
        "the leaf $s mentions $xk but is not a term the TermInterface methods open " *
        "(iscall is false; a wrapper type such as Symbolics' Num must be unwrapped first)"))
    nothing
end
check_leaves(t, xk::String) = isnode(t) ? foreach(a -> check_leaves(a, xk), arguments(t)) : check_leaf(t, xk)

# the term t as an indeterminate of the constant field (a parameter, step SY; an opaque
# subterm, step US); a new one restarts the parse over the larger field
function sym_const(T::Tower, t)
    g = ConstGen(:sym, Q(0), t)
    j = findfirst(==(g), T.consts)
    if j === nothing
        # each parameter nests the constant field one level deeper; the arithmetic cost grows steeply
        # (four parameters did not finish in minutes), so their number is capped
        count(c -> c.kind === :sym, T.consts) < MAX_PARAMS || throw(RischNotImplemented(
            "more than $MAX_PARAMS symbolic parameters"))
        throw(NewConstants(ConstGen[T.consts; g]))
    end
    lconst(T, tgen(ctype(T), j), 0)
end

# Build the tower for `f`. A Restart (a rational multiple such as exp(x/2) after
# exp(x)) refines the generator and re-parses; the hints only ever grow. A NewConstants
# (a constant such as e or log 2 appeared) re-parses over the larger field ℚ(t₁, …, tₖ).
# `constants` fixes the constant field instead (no constant generators can then be added).
function build_tower(f, xk::String; constants::Union{Nothing,Type} = nothing, subst = nothing, minimize::Bool = true)
    @nospecialize f
    scales = Dict{Int,Int}()
    consts = ConstGen[]
    base = Q                                   # becomes ℚ(i) when trigonometric functions appear
    for _ in 1:50
        C = constants === nothing ? cfield(length(consts), base) : constants
        T = Tower(C, xk, scales, copy(consts))
        T.subst = subst
        try
            el = parse_tower(f, T)
            return minimize ? minimal(T, el) : (T, el)     # (minimize = false: levels a parse hook used stay)
        catch e
            if e isa Restart
                scales[e.seq] = lcm(get(scales, e.seq, 1), e.q)
            elseif e isa NewConstants
                constants === nothing || throw(RischNotImplemented(
                    "the input involves transcendental constants, but the constant field was fixed to $constants"))
                length(e.consts) <= MAX_CONSTS || throw(RischNotImplemented(
                    "more than $MAX_CONSTS transcendental constants"))
                consts = e.consts
            elseif e isa NeedComplex
                constants === nothing || throw(RischNotImplemented(
                    "trigonometric input needs the constant field ℚ(i), but it was fixed to $constants"))
                base = QI
            else
                rethrow()
            end
        end
    end
    throw(RischError("could not find a consistent exponential generator"))
end

# drop top levels that the element does not involve
function minimal(T::Tower, el)
    i = levelof(T, el)
    while i > 0 && isone(el.den) && degree(el.num) <= 0
        el = isempty(el.num.c) ? zero(T.Ts[i]) : el.num.c[1]
        i -= 1
    end
    resize!(T.levels, i)
    resize!(T.Ts, i + 1)
    T, el
end

# --- tower element -> term ----------------------------------------------------
function theta_term(b::Builder, T::Tower, i::Int)
    lv = T.levels[i]
    mk(b, lv.kind, tower_to_term(b, T, lv.arg))
end
function poly_theta_term(b::Builder, T::Tower, i::Int, p)
    iszero(p) && return b.lift(0)
    ts = Any[]
    for (k, c) in enumerate(p.c)
        iszero(c) && continue
        ct = tower_to_term(b, T, c)
        e = k - 1
        if e == 0
            push!(ts, ct)
        else
            th = theta_term(b, T, i)
            thk = e == 1 ? th : mk(b, :^, th, b.lift(e))
            push!(ts, isone(c) ? thk : mk(b, :*, ct, thk))
        end
    end
    length(ts) == 1 ? ts[1] : mk(b, :+, ts...)
end
function tower_to_term(b::Builder, T::Tower, f)
    i = levelof(T, f)
    i == 0 && return frac_term(b, f)
    n = poly_theta_term(b, T, i, f.num)
    isone(f.den) ? n : mk(b, :/, n, poly_theta_term(b, T, i, f.den))
end

function describe(T::Tower)
    b = Builder((op, args...) -> Expr(:call, nameof(op), args...), identity, Symbol(T.xk))
    join(("θ$i = " * string(theta_term(b, T, i)) for i in eachindex(T.levels)), ", ")
end

"""
    tower_derivative(f, x; build = nothing, lift = nothing)

Differentiate `f` with the tower derivation (parse -> D -> term). Mainly a test of
the Stage 2 machinery: the result must agree with the ordinary derivative.
"""
function tower_derivative(f, x; build = nothing, lift = nothing)
    @nospecialize f x
    T, el = build_tower(f, string(x))
    d = D(T, el)
    b = Builder(build === nothing ? auto_build(f, x) : build,
                lift === nothing ? auto_lift(f, x) : lift, x, T.consts)
    is_complex_field(ctype(T)) && return real_term(b, T, sigma_kinds(T), d)
    tower_to_term(b, T, d)
end
