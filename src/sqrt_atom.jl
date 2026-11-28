# ---------------------------------------------------------------------------
# Step SQ: half-integer powers of B = a₀ + a₁ A, A = log(V), asin(u), acos(u), asinh(u), acosh(u) or W(u), u linear
# (√(log(a xⁿ)) x³, x²/(a + b asin(c x))^(3/2), 1/√(acos(a x)), (a + b asinh(c x))^(7/2), √(c W(a + b x)); samples
# 1186, 2289, 2336, 2709, 2980): w = √B, A = T(w) = (w² - a₀)/a₁, and x from A:
#   asin: x = (sin T - d)/c, √(k (1 - u²)) = √k cos T;  acos: (cos T - d)/c, √k sin T;  asinh: (sinh T - d)/c, √k cosh T;
#   acosh: (cosh T - d)/c, √k sinh T (u ≥ 1);  W: (T eᵀ - d)/c;
#   log: A′ = k/(x + h) (V = c (x + h)^k, the exponents symbolic too), so x + h = κ e^(A/k) with κ = (x + h) e^(-A/k)
#   a constant, kept as a symbol in the integral and put back after.
# Then ∫ f dx = ∫ f(x(w)) x′(T) 2w/a₁ dw, a polynomial (or even negative powers) in w times exponentials and sines of
# quadratics in w: step GT, GQ (erf for Rubi's erf, erfi, FresnelS, FresnelC). w ↦ √B back; checked numerically.
# Nothing when f has another atom, another half-integer power of an atom, or the integral in w is refused.
# ---------------------------------------------------------------------------
const SQ_ATOMS = (:log, :asin, :acos, :asinh, :acosh, :lambertw, :LambertW, :atan)

try_sqrt_atom(f, x; build = nothing, lift = nothing, verify::Bool = true) =
    integrate_rewritten_expr(f, x, (fe, xs) -> nothing, SQ_ACTIVE; build = build, lift = lift, verify = verify,
                             answer = (fe, xs) -> sqrt_atom_expr(fe, xs; verify = verify))

function sqrt_atom_expr(fe, xs::Symbol; verify::Bool = true)
    # (Rubi's LambertW as lambertw, which the numeric check evaluates; the answer in the input's name)
    ren(t, a, b) = t isa Expr ? Expr(t.head, (t.head === :call && i == 1 && s === a ? b : ren(s, a, b) for (i, s) in enumerate(t.args))...) : t
    hasop(t, n) = t isa Expr && ((t.head === :call && t.args[1] === n) || any(s -> hasop(s, n), t.args))
    if hasop(fe, :LambertW)
        G = sqrt_atom_expr(ren(fe, :LambertW, :lambertw), xs; verify = verify)
        return G === nothing ? nothing : ren(G, :lambertw, :LambertW)
    end
    xk = string(xs)
    iscall(t, n, k) = t isa Expr && t.head === :call && t.args[1] === n && length(t.args) == k + 1
    isatom(t) = t isa Expr && t.head === :call && t.args[1] in SQ_ATOMS && length(t.args) == 2 && has_x(t.args[2], xk)
    atoms!(acc, t) = (isatom(t) ? push!(acc, t) : t isa Expr && foreach(a -> atoms!(acc, a), t.args); acc)
    half(t) = iscall(t, :sqrt, 1) ? (t.args[2], Q(1 // 2)) :
              (iscall(t, :^, 2) && (p = leaf_rational(t.args[3]); p !== nothing && denominator(p) == 2)) ? (t.args[2], Q(p)) : nothing
    # the half-integer powers of B, one B with one atom A; every atom of f is A
    Bs = Any[]
    walk(t) = t isa Expr && ((h = half(t); h !== nothing && !isempty(atoms!(Any[], h[1])) && push!(Bs, h[1])); foreach(walk, t.args))
    walk(fe)
    as = unique(atoms!(Any[], fe))
    # no atom: half-integer powers of one linear P with exp, sin, cos of x, P itself as A, w = √P ((d x)^(3/2) sin(f x),
    # cos(a + b x)³/(c + d x)^(5/2), samples 1351, 1566)
    lin = false
    if isempty(as)
        Ps = Any[]
        walkp(t) = t isa Expr && ((h = half(t); h !== nothing && has_x(h[1], xk) && push!(Ps, h[1])); foreach(walkp, t.args))
        walkp(fe)
        (isempty(Ps) || !all(==(Ps[1]), Ps)) && return nothing
        hastrig(t) = t isa Expr && ((t.head === :call && t.args[1] in (:exp, :sin, :cos, :sinh, :cosh) && length(t.args) == 2 &&
                                     has_x(t.args[2], xk)) || any(hastrig, t.args))
        hastrig(fe) || return nothing
        Bs, as, lin = Any[Ps[1]], Any[Ps[1]], true
    end
    length(as) == 1 || return nothing
    A = as[1]
    # without a half-integer power: w = A itself, for an A in an exp or trigonometric argument (xᵐ e^((a + b log(c xⁿ))²),
    # the second integral of x² erfi(d (a + b log(c xⁿ))) by parts, sample 2931)
    direct = isempty(Bs)
    if direct
        inarg(t) = t isa Expr && ((t.head === :call && t.args[1] in (:exp, :sin, :cos, :sinh, :cosh) && length(t.args) == 2 &&
                                   !isempty(atoms!(Any[], t.args[2]))) || any(inarg, t.args))
        inarg(fe) || return nothing
        Bs = Any[A]
    end
    B = Bs[1]
    all(==(B), Bs) || return nothing
    name, u = lin ? (:lin, A) : (A.args[1], A.args[2])
    # (log(u + √(u² + 1)): asinh as another step rewrote it; step SQ takes asinh itself, with a simpler answer)
    hasrad(t) = t isa Expr && (half(t) !== nothing || any(hasrad, t.args))
    (name === :log && hasrad(u)) && return nothing
    rep(t, a, b) = t == a ? b : t isa Expr ? Expr(t.head, (rep(s, a, b) for s in t.args)...) : t
    tw(t, v) = try
        build_tower(t, v)
    catch err
        (err isa RischNotImplemented || err isa RischError || err isa NeedComplex || err isa DivideError) || rethrow()
        (nothing, nothing)
    end
    ct(T, c, v) = cterm_complex(Builder(expr_build, identity, v, T.consts), c, T.consts)
    # B = a₀ + a₁ A
    τ = gensym("τ")
    Bτ = rep(B, A, τ)
    has_x(Bτ, xk) && return nothing
    TB, eB = tw(Bτ, string(τ))
    (TB !== nothing && isempty(TB.levels) && degree(eB.den) == 0 && degree(eB.num) == 1) || return nothing
    a0 = ct(TB, eB.num.c[1] / eB.den.c[1], τ)
    a1 = ct(TB, eB.num.c[2] / eB.den.c[1], τ)
    a0z = leaf_rational(a0) == 0
    w = gensym("w")
    Tw = a0z ? :($w ^ 2 / $a1) : :(($w ^ 2 - $a0) / $a1)
    leaf_rational(a1) == 1 && (Tw = a0z ? :($w ^ 2) : :($w ^ 2 - $a0))
    direct && (Tw = w)
    κ = gensym("κ")
    κx = nothing
    rad = nothing                                    # P with √P ↦ √k R(T): (1 - u², R) for asin, ...
    xpow = t -> nothing
    halfangle = false
    # atan(c x): x = tan T/c, a product of xᵏ, (k (1 + c² x²))^p, Bᵖ and constants as c⁻ᵏ sinᵏT cos^(-k)T, kᵖ cos^(-2p)T
    # (cos T > 0 for T = atan(c x)), wᵖ; dx = dT/(c cos²T); the exponents of sin, cos must come out ≥ 0 (√atan(a x)/(c +
    # a² c x²)², samples 2377–2381). Nothing for a sum, or atan(c x + d) with d ≠ 0
    function atan_product(t0)
        Tu, eu = tw(u, xk)
        (Tu !== nothing && isempty(Tu.levels) && degree(eu.den) == 0 && degree(eu.num) == 1 && iszero(eu.num.c[1])) || return nothing
        c1 = ct(Tu, eu.num.c[2] / eu.den.c[1], xs)
        lv = Any[]
        function facs(t, e)
            if iscall(t, :*, length(t isa Expr ? t.args : []) - 1) && t.args[1] === :*
                foreach(v -> facs(v, e), t.args[2:end])
            elseif iscall(t, :/, 2)
                facs(t.args[2], e); facs(t.args[3], -e)
            elseif iscall(t, :sqrt, 1) && t.args[2] != B
                facs(t.args[2], e / 2)
            elseif iscall(t, :^, 2) && t.args[2] != B && (p = leaf_rational(t.args[3]); p !== nothing) &&
                   !(t.args[2] isa Expr && t.args[2].head === :call && t.args[2].args[1] in (:+, :-))
                facs(t.args[2], e * Q(p))
            else
                (hp = half(t); hp !== nothing && hp[1] == B) ? push!(lv, (B, e * hp[2])) :
                (iscall(t, :^, 2) && (p = leaf_rational(t.args[3]); p !== nothing)) ? push!(lv, (t.args[2], e * Q(p))) :
                push!(lv, (t, e))
            end
        end
        facs(t0, Q(1))
        ks, ns, cs = Q(0), Q(-2), Any[:(1 / $c1)]      # sin, cos exponents; dx = dT/(c cos²T)
        wp = Q(0)
        for (v, e) in lv
            if !has_x(v, xk)
                push!(cs, isone(e) ? v : :($v ^ $e))
            elseif v == xs
                isinteger(e) || return nothing
                ks += e; ns -= e; push!(cs, :($c1 ^ $(-e)))
            elseif v == B
                wp += 2e
            elseif v == A && B == A
                wp += 2e
            else
                isempty(atoms!(Any[], v)) || return nothing
                Tk, ek = tw(:($v / (1 + $u ^ 2)), xk)
                (Tk !== nothing && isempty(Tk.levels) && degree(ek.num) == 0 && degree(ek.den) == 0) || return nothing
                kc = ct(Tk, ek.num.c[1] / ek.den.c[1], xs)
                leaf_rational(kc) == 1 || push!(cs, :($kc ^ $e))
                ns -= 2e
            end
        end
        (isinteger(ks) && isinteger(ns) && isinteger(wp) && ks >= 0 && ns >= 0) || return nothing
        fs = Any[cs..., :(2 * $w ^ $(Int(wp) + 1) / $a1)]
        ks > 0 && push!(fs, :(sin($Tw) ^ $(Int(ks))))
        ns > 0 && push!(fs, :(cos($Tw) ^ $(Int(ns))))
        Expr(:call, :*, fs...)
    end
    if name === :atan
        nothing
    elseif name === :lin
        Tl, el_ = tw(A, xk)
        (Tl !== nothing && isempty(Tl.levels) && degree(el_.den) == 0 && degree(el_.num) == 1) || return nothing
        c1 = ct(Tl, el_.num.c[2] / el_.den.c[1], xs)
        d0 = ct(Tl, el_.num.c[1] / el_.den.c[1], xs)
        xof = T -> leaf_rational(d0) == 0 ? :($T / $c1) : :(($T - $d0) / $c1)
        dxdT = T -> :(1 / $c1)
    elseif name === :asin && (Tq = first(tw(u, xk)); Tq !== nothing && isempty(Tq.levels)) &&
           (eq = last(tw(u, xk)); degree(eq.den) == 0 && degree(eq.num) == 2 && iszero(eq.num.c[2]) &&
            crational(eq.num.c[1] / eq.den.c[1]) in (1, -1))
        # asin(±1 + d x²): 1 ∓ sin T = (cos(T/2) ∓ sin(T/2))², so x = κ (cos(T/2) ∓ sin(T/2)) with κ = x/(cos(A/2) ∓ sin(A/2))
        # constant (κ² = ∓1/d), as Rubi writes it (samples 2328, 2329)
        sg = crational(eq.num.c[1] / eq.den.c[1]) == 1 ? :- : :+
        halfangle = true
        κx = Expr(:call, :/, xs, Expr(:call, sg, :(cos($A / 2)), :(sin($A / 2))))
        xof = T -> :($κ * $(Expr(:call, sg, :(cos($T / 2)), :(sin($T / 2)))))
        dxdT = T -> sg === :- ? :(-($κ) * (sin($T / 2) + cos($T / 2)) / 2) : :($κ * (cos($T / 2) - sin($T / 2)) / 2)
    elseif name in (:asin, :acos, :asinh, :acosh, :lambertw, :LambertW)
        Tu, eu = tw(u, xk)
        (Tu !== nothing && isempty(Tu.levels) && degree(eu.den) == 0 && degree(eu.num) == 1) || return nothing
        c1 = ct(Tu, eu.num.c[2] / eu.den.c[1], xs)
        d0 = ct(Tu, eu.num.c[1] / eu.den.c[1], xs)
        S, dS, rad = name === :asin ? (:sin, T -> :(cos($T)), (:(1 - $u ^ 2), :cos)) :
                     name === :acos ? (:cos, T -> :(-(sin($T))), (:(1 - $u ^ 2), :sin)) :
                     name === :asinh ? (:sinh, T -> :(cosh($T)), (:(1 + $u ^ 2), :cosh)) :
                     name === :acosh ? (:cosh, T -> :(sinh($T)), (:($u ^ 2 - 1), :sinh)) :
                     (nothing, T -> :((1 + $T) * exp($T)), nothing)
        xof = T -> (s = S === nothing ? :($T * exp($T)) : :($S($T)); :(($s - $d0) / $c1))
        dxdT = T -> :($(dS(T)) / $c1)
    else                                             # log
        dA = term_deriv(Builder(expr_build, identity, xs), A, xk)
        dA === nothing && return nothing
        Td, ed = tw(dA, xk)
        (Td !== nothing && isempty(Td.levels) && degree(ed.num) == 0 && degree(ed.den) == 1) || return nothing
        p1, p0, N = ed.den.c[2], ed.den.c[1], ed.num.c[1]
        h, k = ct(Td, p0 / p1, xs), ct(Td, N / p1, xs)
        xh = leaf_rational(h) == 0 ? xs : :($xs + $h)
        κx = :($xh * exp(-($A) / $k))
        xof = T -> leaf_rational(h) == 0 ? :($κ * exp($T / $k)) : :($κ * exp($T / $k) - $h)
        dxdT = T -> :($κ * exp($T / $k) / $k)
        # (c x)^p, x^p with p not a number and h = 0: c^p κ^p e^(p T/k) (x^m e^((a + b log(c xⁿ))²), sample 2932)
        if leaf_rational(h) == 0
            xpow = function (t)
                (iscall(t, :^, 2) && !has_x(t.args[3], xk) && leaf_rational(t.args[3]) === nothing) || return nothing
                bs, p = t.args[2], t.args[3]
                c = bs == xs ? nothing : (iscall(bs, :*, 2) && bs.args[3] == xs && !has_x(bs.args[2], xk)) ? bs.args[2] :
                    (iscall(bs, :*, 2) && bs.args[2] == xs && !has_x(bs.args[3], xk)) ? bs.args[3] : false
                c === false && return nothing
                e = :($κ ^ $p * exp($p * $Tw / $k))
                c === nothing ? e : :($c ^ $p * $e)
            end
        end
    end
    # √P, P^(m/2) with P = k·(the radicand of rad): √k^m R(T)^m
    function radsub(t)
        (rad === nothing || !(t isa Expr)) && return nothing
        hp = half(t)
        hp === nothing && return nothing
        P, p = hp
        has_x(P, xk) || return nothing
        isempty(atoms!(Any[], P)) || return nothing
        Tk, ek = tw(:($P / $(rad[1])), xk)
        (Tk !== nothing && isempty(Tk.levels) && degree(ek.num) == 0 && degree(ek.den) == 0) || return nothing
        kc = ct(Tk, ek.num.c[1] / ek.den.c[1], xs)
        m = Int(2p)
        R = :($(rad[2])($Tw) ^ $m)
        leaf_rational(kc) == 1 ? R : :($kc ^ $(p) * $R)
    end
    function sub(t)
        if t isa Expr
            hp = half(t)
            hp !== nothing && hp[1] == B && return :($w ^ $(Int(2 * hp[2])))
            r = radsub(t)
            r === nothing || return r
            r = xpow(t)
            r === nothing || return r
            t == A && return Tw
            return Expr(t.head, (sub(s) for s in t.args)...)
        end
        t == xs ? xof(Tw) : t
    end
    g = name === :atan ? atan_product(fe) :
        direct ? :($(sub(fe)) * $(dxdT(Tw))) : :($(sub(fe)) * $(dxdT(Tw)) * 2 * $w / $a1)
    g === nothing && return nothing
    has_x(g, xk) && return nothing
    G = try
        risch_integrate(g, w; build = expr_build, lift = identity, verify = verify)
    catch err
        (err isa RischNotImplemented || err isa NotElementary) || rethrow()
        return nothing
    end
    (G === nothing || G isa IntegralWithRootSums) && return nothing
    # w^q ↦ B^(q/2), w ↦ √B, κ ↦ (x + h) e^(-A/k)
    function back(t)
        t == w && return direct ? A : :(sqrt($B))
        t == κ && return κx
        t isa Expr || return t
        # exp, sin, ... of c₂ w² + c₀: of (c₂ a₁) A + (c₂ a₀ + c₀), e^(2 asinh u), not e^(-a/b + (a + b asinh u)/b)
        if t.head === :call && t.args[1] in (:exp, :sin, :cos, :sinh, :cosh) && length(t.args) == 2 && has_x(t.args[2], string(w))
            aτ = direct ? rep(t.args[2], w, τ) : rep(t.args[2], :($w ^ 2), Bτ)
            if !has_x(aτ, string(w))
                Ta, ea = tw(aτ, string(τ))
                if direct && Ta !== nothing && isempty(Ta.levels) && degree(ea.den) == 0 && 1 <= degree(ea.num) <= 4
                    # (w = A: the argument as Σ cⱼ Aʲ)
                    ts = Any[]
                    for j in degree(ea.num):-1:0
                        c = ea.num.c[j + 1] / ea.den.c[1]
                        iszero(c) && continue
                        cj = ct(Ta, c, τ)
                        Aj = j == 0 ? nothing : j == 1 ? A : :($A ^ $j)
                        push!(ts, Aj === nothing ? cj : leaf_rational(cj) == 1 ? Aj : :($cj * $Aj))
                    end
                    return Expr(:call, t.args[1], length(ts) == 1 ? ts[1] : Expr(:call, :+, ts...))
                end
                if Ta !== nothing && isempty(Ta.levels) && degree(ea.den) == 0 && degree(ea.num) <= 1
                    m = degree(ea.num) == 1 ? ct(Ta, ea.num.c[2] / ea.den.c[1], τ) : 0
                    r = ct(Ta, ea.num.c[1] / ea.den.c[1], τ)
                    mA = leaf_rational(m) == 0 ? nothing : leaf_rational(m) == 1 ? A : :($m * $A)
                    arg = mA === nothing ? r : leaf_rational(r) == 0 ? mA : :($mA + $r)
                    # e^(m W(u)) = (u/W(u))ᵐ, m an integer (as step LW writes it)
                    mq = leaf_rational(m)
                    (name === :lambertw && t.args[1] === :exp && leaf_rational(r) == 0 && mq !== nothing && isinteger(mq) &&
                     !iszero(mq)) && return isone(mq) ? :($u / $A) : :(($u / $A) ^ $(Int(mq)))
                    return Expr(:call, t.args[1], arg)
                end
            end
        end
        if iscall(t, :^, 2) && t.args[2] == w && (q = leaf_rational(t.args[3]); q !== nothing)
            e = direct ? Q(q) : Q(q) / 2
            return isone(e) ? B : :($B ^ $(isone(denominator(e)) ? Int(e) : e))
        end
        Expr(t.head, (back(s) for s in t.args)...)
    end
    Gx = back(G)
    # (W(u): no numeric W here, and x = (w eʷ - d)/c, w = √B are identities, as for step LW)
    if verify && name !== :lambertw && !numeric_antiderivative(fe, Gx, xk)
        # (asin(1 + d x²) with the check's d > 0 is complex at every point: compared as complex values there, two points)
        halfangle || return nothing
        ev = numeric_evaluator(xk, fe, Gx)
        ok = 0
        for x0 in (0.3, 0.7, -0.5, 1.3)
            fv, dG = try
                ev(fe, x0), (ev(Gx, x0 + 1e-6) - ev(Gx, x0 - 1e-6)) / 2e-6
            catch
                continue
            end
            (isfinite(fv) && isfinite(dG)) || continue
            abs(dG - fv) <= 1e-5 * max(1.0, abs(fv)) || return nothing
            ok += 1
        end
        ok >= 2 || return nothing
    end
    Gx
end
