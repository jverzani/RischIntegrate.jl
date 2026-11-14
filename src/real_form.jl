# ---------------------------------------------------------------------------
# Step 7: real form of results over ℚ(i)
#
# Complex conjugation σ (i ↦ -i, x real) acts on a tower whose generators are real
# (exp or log of real elements: σθ = θ) or trigonometric (θ = exp(i·w), w real: σθ = 1/θ).
# σ commutes with the derivation, so for a real integrand f and ∫ f = F computed over ℚ(i),
# Re F = (F + σF)/2 is an antiderivative too, and it has a real form:
#   (v + σv)/2                      σ-invariant; on a :trig level written with cos(kw), sin(kw)
#   (c log w + σc log σw)/2   =     c_r/2 log(w σw) - c_i atan(V/U)
#       c_r = (c + σc)/2, c_i = (c - σc)/(2i), U = (w + σw)/2, V = (w - σw)/(2i)
#   (c_r log w when w is real). The real form is re-verified exactly in the tower.
# ---------------------------------------------------------------------------
function sigma_kinds(T::Tower)
    kinds = Symbol[]
    for (i, lv) in enumerate(T.levels)
        sa = tconj(T, kinds, lv.arg, levelof(T, lv.arg))
        if sa == lv.arg
            push!(kinds, :real)
        elseif lv.kind === :exp && sa == -lv.arg
            push!(kinds, :trig)
        else
            throw(RischNotImplemented(
                "generator $i ($(lv.kind)) is neither real nor exp(i·real): no real form"))
        end
    end
    kinds
end

# step EC: exp(w) with w = α + iβ, α and β real rational functions of x, neither zero (exp((1 + i) z), SymPy #20034):
# exp(α) exp(iβ), whose generators are real and exp(i·real), where exp(w) alone is neither. f rewritten so, or nothing
# (i as a leaf, a Complex number, or a node: SymJ's (-1)^(1/2))
has_complex_leaf(t) = is_imag_unit(t) || (isnode(t) ? any(has_complex_leaf, arguments(t)) : (t isa Complex && !iszero(imag(t))))
function split_complex_exps(f, x, build, lift)
    @nospecialize f x
    xk = string(x)
    b0 = Builder(build === nothing ? auto_build(f, x) : build, lift === nothing ? auto_lift(f, x) : lift, x)
    changed = false
    function rw(t)
        isnode(t) || return t
        args = Any[rw(a) for a in arguments(t)]
        n = opname(operation(t))
        # exp(w), or ℯ^w (SymJ's exp)
        w = (n === :exp && length(args) == 1) ? args[1] :
            (n === :^ && length(args) == 2 && is_e_const(args[1])) ? args[2] : nothing
        if w !== nothing && depends_on(w, xk) && has_complex_leaf(w)
            p = complex_rational_parts(w, xk, b0)
            if p !== nothing && p[1] !== nothing && p[2] !== nothing
                changed = true
                return mk(b0, :*, mk(b0, :exp, p[1]), mk(b0, :exp, mk(b0, :*, b0.lift(im), p[2])))
            end
        end
        term_rebuild(b0, t, args)
    end
    g = rw(f)
    changed ? g : nothing
end

# ∫ f by a rewrite `rw(fe, x)` of its Expr form fe (nothing: no change), integrated through Expr and put back in the
# user's terms: a term type may undo the rewrite (SymJ merges exp(α) exp(iβ) back into exp(α + iβ), e^(-c x) e^(c y)
# into e^(-c (x - y))), which looped refusal and rewrite. `active` guards against the rewrite inside its own integral.
function integrate_rewritten_expr(f, x, rw, active; build = nothing, lift = nothing, verify::Bool = true)
    @nospecialize f x
    active[] && return nothing
    xk = string(x)
    leaves = Dict{String,Any}()
    collect_leaves!(leaves, f)
    toexpr(t) = is_imag_unit(t) ? :im : (safe_iscall(t) && !isempty(arguments(t))) ?
        Expr(:call, opname(operation(t)), (toexpr(a) for a in arguments(t))...) : term_to_expr(t)
    g = rw(toexpr(f), Symbol(xk))
    g === nothing && return nothing
    active[] = true
    F = try
        risch_integrate(g, Symbol(xk); build = expr_build, lift = identity, verify = verify)
    finally
        active[] = false
    end
    F isa IntegralWithRootSums && return nothing
    f isa Expr && return F
    b0 = Builder(build === nothing ? auto_build(f, x) : build, lift === nothing ? auto_lift(f, x) : lift, x)
    function back(ex)                                   # Expr → the user's term type
        ex === :im && return b0.lift(im)
        ex isa Symbol && return haskey(leaves, string(ex)) ? leaves[string(ex)] : ex === :ℯ ? mk(b0, :exp, b0.lift(1)) : ex
        ex isa Number && return b0.lift(ex)
        ex isa Expr && ex.head === :call || return ex
        b0.build(op_function(ex), (back(a) for a in ex.args[2:end])...)
    end
    back(F)
end
integrate_split_complex_exps(f, x; build = nothing, lift = nothing, verify::Bool = true) =
    integrate_rewritten_expr(f, x, (fe, xs) -> split_complex_exps(fe, xs, expr_build, identity), EC_ACTIVE;
                             build = build, lift = lift, verify = verify)

# σ on an element of level i (needs the kinds of levels 1..i)
function tconj(T::Tower, kinds, f, i::Int)
    i == 0 && return conj_frac(cpconj_g(T.consts, f.num), cpconj_g(T.consts, f.den))   # x real
    iszero(f) && return f
    n = tconj_poly(T, kinds, f.num, i)
    d = tconj_poly(T, kinds, f.den, i)
    kinds[i] === :real && return conj_frac(n, d)
    # θ ↦ 1/θ: p(θ) ↦ θ^(-deg p) p̃(θ), p̃ = reversed conjugated coefficients (n, d)
    conj_frac_rev(n, d, degree(f.num), degree(f.den))
end
function tconj_poly(T::Tower, kinds, p::UPoly, i::Int)
    K = T.Ts[i]
    cs = K[tconj(T, kinds, c, i - 1) for c in p.c]
    kinds[i] === :trig && reverse!(cs)
    UPoly{K}(cs)
end

# Laurent polynomials in θ as Dict(k => coefficient)
laurent_of(p::UPoly{K}) where {K} = Dict{Int,K}(k - 1 => c for (k, c) in enumerate(p.c) if !iszero(c))
laurent_conj(T::Tower, kinds, p::UPoly{K}, i::Int) where {K} =        # Σ σ(c_k) θ^(-k)
    Dict{Int,K}(-(k - 1) => tconj(T, kinds, c, i - 1) for (k, c) in enumerate(p.c) if !iszero(c))
function laurent_mul(a::Dict{Int,K}, b::Dict{Int,K}) where {K}
    r = Dict{Int,K}()
    for (i, x) in a, (j, y) in b
        s = get(r, i + j, zero(K)) + x * y
        iszero(s) ? delete!(r, i + j) : (r[i + j] = s)
    end
    r
end

# a σ-invariant element of level i as a real term
function real_term(b::Builder, T::Tower, kinds, f, i::Int = levelof(T, f))
    i == 0 && return frac_term(b, f)            # σ-invariant: real coefficients (cterm checks)
    lv = T.levels[i]
    if kinds[i] === :real
        th = mk(b, lv.kind, real_term(b, T, kinds, lv.arg))
        n = real_poly_term(b, T, kinds, f.num, i, th)
        return isone(f.den) ? n : mk(b, :/, n, real_poly_term(b, T, kinds, f.den, i, th))
    end
    # :trig, θ = exp(i w):  f = N/D = (N·σD)/(D·σD) with σ-invariant Laurent numerator and denominator
    sD = laurent_conj(T, kinds, f.den, i)
    A = laurent_mul(laurent_of(f.num), sD)
    B = laurent_mul(laurent_of(f.den), sD)
    C = ctype(T)
    w = liftto(T, lv.arg, i - 1) * lconst(T, -cimag(C), i - 1)
    wt = real_term(b, T, kinds, w)
    num = real_laurent_term(b, T, kinds, A, i, wt)
    if length(B) == 1 && haskey(B, 0)
        return isone(B[0]) ? num : mk(b, :/, num, real_term(b, T, kinds, B[0], i - 1))
    end
    F = mk(b, :/, num, real_laurent_term(b, T, kinds, B, i, wt))
    # with a pole at θ = -1 (θ = 1) the answer is singular there anyway: as a rational function of tan(w/2)
    # (cot(w/2)) it is often much shorter (∫ tan² x = tan x - x); the shortest form is kept
    # in Θ = θ^g when f is a function of θ^g (∫ tan² x: θ = e^(ix), poles θ = ±i, Θ = -1)
    g = 0
    for p in (f.num, f.den), (k, c) in enumerate(p.c)
        iszero(c) || (g = gcd(g, k - 1))
    end
    g = max(g, 1)
    cg(p) = typeof(p)(p.c[1:g:end])
    fg = (cg(f.num), cg(f.den))
    best, len = F, length(string(F))
    for (θ0, fn) in ((-1, :tan), (1, :cot))
        iszero(peval(fg[2], θ0 * one(eltype(f.den.c)))) || continue
        G = tan_form_term(b, T, kinds, fg, g, i, fn)
        G === nothing && continue
        l = length(string(G))
        l < len && ((best, len) = (G, l))
    end
    best
end

# f = n(Θ)/d(Θ), Θ = θ^g = e^(igw), n, d over K_{i-1}, as a rational function of t = tan(gw/2)
# (Θ = (1 + it)/(1 - it)) or t = cot(gw/2) (Θ = (t + i)/(t - i)) with real coefficients, printed as
# q(t) + r(t)/d(t); nothing if the coefficients are not real (they are, for σ-invariant f, once d is monic)
function tan_form_term(b::Builder, T::Tower, kinds, (fnum, fden), g::Int, i::Int, fn::Symbol)
    K = eltype(fnum.c)
    P = UPoly{K}
    C = ctype(T)
    I = lconst(T, cimag(C), i - 1)
    o = one(K)
    nθ, dθ = fn === :tan ? (P(K[o, I]), P(K[o, -I])) : (P(K[I, o]), P(K[-I, o]))
    m = max(degree(fnum), degree(fden))
    sub(p) = sum(scale(p.c[k + 1], nθ^k * dθ^(m - k)) for k in 0:degree(p))
    N, D = sub(fnum), sub(fden)
    h = gcd(N, D)
    N, D = quo(N, h), quo(D, h)
    l = lc(D)
    N, D = scale_div(N, l), scale_div(D, l)
    all(c -> tconj(T, kinds, c, i - 1) == c, vcat(N.c, D.c)) || return nothing
    w2 = liftto(T, T.levels[i].arg, i - 1) * lconst(T, -cimag(C) * cfromQ(C, Q(g, 2)), i - 1)   # g w/2
    tt = mk(b, fn, real_term(b, T, kinds, w2))
    q, r = divrem(N, D)
    pt(p) = real_poly_term(b, T, kinds, p, i, tt)
    ts = Any[]
    iszero(q) || push!(ts, pt(q))
    iszero(r) || push!(ts, degree(D) == 0 ? pt(r) : mk(b, :/, pt(r), pt(D)))
    isempty(ts) ? b.lift(0) : length(ts) == 1 ? ts[1] : mk(b, :+, ts...)
end

function real_poly_term(b::Builder, T::Tower, kinds, p::UPoly, i::Int, th)
    iszero(p) && return b.lift(0)
    ts = Any[]
    for (k, c) in enumerate(p.c)
        iszero(c) && continue
        e = k - 1
        if e == 0
            push!(ts, real_term(b, T, kinds, c, i - 1))
        else
            thk = e == 1 ? th : mk(b, :^, th, b.lift(e))
            push!(ts, isone(c) ? thk : mk(b, :*, real_term(b, T, kinds, c, i - 1), thk))
        end
    end
    length(ts) == 1 ? ts[1] : mk(b, :+, ts...)
end

# Σ a_k θ^k with a_(-k) = σ(a_k):  a_0 + Σ_(k>0) (a_k + a_(-k)) cos(kw) + i(a_k - a_(-k)) sin(kw)
function real_laurent_term(b::Builder, T::Tower, kinds, L::Dict, i::Int, wt)
    K = T.Ts[i]
    all(k -> haskey(L, -k), keys(L)) || throw(RischError("real form: Laurent polynomial is not σ-invariant"))
    I = lconst(T, cimag(ctype(T)), i - 1)
    ts = Any[]
    c0 = get(L, 0, zero(K))
    iszero(c0) || push!(ts, real_term(b, T, kinds, c0, i - 1))
    for k in sort([k for k in keys(L) if k > 0])
        ck, cm = L[k], L[-k]
        kw = k == 1 ? wt : mk(b, :*, b.lift(k), wt)
        for (coef, fn) in ((ck + cm, :cos), (I * (ck - cm), :sin))
            iszero(coef) && continue
            tr = mk(b, fn, kw)
            push!(ts, isone(coef) ? tr : mk(b, :*, real_term(b, T, kinds, coef, i - 1), tr))
        end
    end
    isempty(ts) && return b.lift(0)
    length(ts) == 1 ? ts[1] : mk(b, :+, ts...)
end

# --- continuous arguments (step TC) ----------------------------------------------
# Re(c log w) = Re c·log|w| - Im c·arg w. The piece atan(V/U) for arg w jumps where U = 0. When
# w = Σ c_k z^k has constant coefficients (c_k ∈ C = ℚ(i) or ℚ(i)(√d)) and z is a real variable
# (x at the base, θ at a real exp/log level), w = A(z) + i B(z) with A, B real polynomials and
# Rioboo's LogToAtan gives arg w ≡ -Σ atan(pⱼ(z)), continuous. At a trig level θ = e^{iu}, with
# t = tan(u/2) (θ = (1 + it)/(1 - it)):  w(θ) = (1 - it)^(-n) w̃(t), w̃(t) = Σ c_k (1+it)^k (1-it)^(n-k),
# so arg w = n·u/2 + arg w̃(t) on (-π, π), and arg w̃ ≡ -Σ atan(pⱼ(t)). At u = π mod 2π (t = ±∞) each
# odd pⱼ jumps by -sign(lc pⱼ)·π, together mπ; the correction -mπ⌊(u+π)/2π⌋ is -(m/2)(u - 2 atan t):
#   arg w ≡ ((n - m)/2)·u - Σ atan(pⱼ(t)) + m·atan(t)          (continuous for all real u)
# t = -i(θ - 1)/(θ + 1) is a tower element, so every piece is still differentiated and checked
# exactly in `to_term_real`. Pieces: (factor, :atan | :lin, element, printer b -> term).
real_field(::Type{QI}) = Q
real_field(::Type{QSB{d,QI}}) where {d} = QS{d}
real_field(::Type) = nothing
re_part(c::QI) = c.re
im_part(c::QI) = c.im
re_part(c::QSB{d,QI}) where {d} = QS{d}(c.a.re, c.b.re)
im_part(c::QSB{d,QI}) where {d} = QS{d}(c.a.im, c.b.im)
to_complex(::Type{QI}, r::Q) = QI(r, Q(0))
to_complex(::Type{QSB{d,QI}}, r::QS{d}) where {d} = QSB{d,QI}(QI(r.a, Q(0)), QI(r.b, Q(0)))
real_sign(r::Q) = sign(r)
function real_sign(r::QS{d}) where {d}                  # sign of a + b√d, d > 0
    a, b = r.a, r.b
    (sign(a) == sign(b) || iszero(b)) && return sign(a) + (iszero(a) ? sign(b) : 0)
    a^2 > d * b^2 ? sign(a) : sign(b)
end

# p(z) for p over the real field, z a term (printing)
function rpoly_term(b::Builder, p::UPoly, zt)
    ts = Any[]
    for (k, c) in enumerate(p.c)
        iszero(c) && continue
        e = k - 1
        zk = e == 0 ? nothing : (e == 1 ? zt : mk(b, :^, zt, b.lift(e)))
        push!(ts, zk === nothing ? cterm(b, c) : (isone(c) ? zk : mk(b, :*, cterm(b, c), zk)))
    end
    isempty(ts) ? b.lift(0) : (length(ts) == 1 ? ts[1] : mk(b, :+, ts...))
end

# number of times the tan(u/2) form of TC was used (read by `bioche`, step TB)

function continuous_arg_pieces(T::Tower, kinds, j::Int, w)
    C = ctype(T)
    RT = real_field(C)
    RT === nothing && return nothing
    isone(w.den) || return nothing
    cs = C[]
    for c in w.num.c
        v = j == 0 ? c : const_value(T, c)
        v === nothing && return nothing
        push!(cs, v)
    end
    n = length(cs) - 1
    n >= 1 || return nothing
    I = cimag(C)
    P = UPoly{C}
    trig = j > 0 && kinds[j] === :trig
    if trig
        ap, am = P(C[one(C), I]), P(C[one(C), -I])
        wt = sum(scale(cs[k + 1], ap^k * am^(n - k)) for k in 0:n)
        θ = frac(xpoly(T.Ts[j]))
        zel = lconst(T, -I, j) * (θ - one(θ)) / (θ + one(θ))           # t = tan(u/2)
        uel = liftto(T, T.levels[j].arg, j - 1) * lconst(T, -I, j - 1)  # θ = e^{iu}
        uterm = b -> real_term(b, T, kinds, uel)
        zterm = b -> mk(b, :tan, mk(b, :/, uterm(b), b.lift(2)))
    else
        wt = P(cs)
        if j == 0
            zel = frac(xpoly(C))
            zterm = b -> b.x
        else
            lv = T.levels[j]
            zel = frac(xpoly(T.Ts[j]))
            zterm = b -> mk(b, lv.kind, real_term(b, T, kinds, lv.arg))
        end
    end
    A = UPoly{RT}(RT[re_part(c) for c in wt.c])
    B = UPoly{RT}(RT[im_part(c) for c in wt.c])
    (iszero(A) || iszero(B)) && return nothing
    peval_el(p) = foldr((c, acc) -> acc * zel + lconst(T, to_complex(C, c), j), p.c; init = zero(zel))
    out = Any[]
    m = 0
    for p in log_to_atan(A, B)                          # Σ 2 atan(p) ≡ 2 atan(A/B) ≡ -2 arg w̃
        degree(p) <= 0 && continue                      # a constant: derivative 0
        push!(out, (-one(C), :atan, peval_el(p), b -> rpoly_term(b, p, zterm(b))))
        trig && isodd(degree(p)) && (m += Int(real_sign(lc(p))))
    end
    if trig && iseven(n - m)                            # the shortcut without tan(u/2) (step TH)
        sh = shifted_arg_pieces(T, kinds, j, w, (n - m) ÷ 2, uel, uterm)
        sh === nothing || return sh
    end
    trig && (HALF_ANGLE_FORMS[] += 1)                   # the tan(u/2) form is used (see `bioche`)
    if trig
        n != m && push!(out, (cfromQ(C, Q(n - m) // 2), :lin, uel, uterm))
        m != 0 && push!(out, (cfromQ(C, Q(m)), :atan, zel, zterm))
    end
    out
end

# Step TH. At a trig level, w of winding number s around the unit circle (s = (n - m)/2 above):
# arg w = s·u + arg v, v = θ^(-s) w, and v = A + iB with A = (v + σv)/2, B = (v - σv)/(2i) real
# trigonometric polynomials. If A never vanishes on the real line, arg v ≡ atan(B/A) (continuous);
# if B never does, arg v ≡ -atan(A/B). "Never vanishes" is decided exactly: with t = tan(u/2),
# A·(1 + t²)^K = Σ a_k (1+it)^(K+k) (1-it)^(K-k) is a real polynomial without real roots (Sturm), and
# A(π) = Σ a_k (-1)^k ≠ 0. Returns the pieces of arg w, or nothing (then the tan(u/2) form is used).
function shifted_arg_pieces(T::Tower, kinds, j::Int, w, s::Int, uel, uterm)
    C = ctype(T)
    RT = real_field(C)
    I = cimag(C)
    θel = frac(xpoly(T.Ts[j]))
    v = s >= 0 ? w / θel^s : w * θel^(-s)
    sv = tconj(T, kinds, v, j)
    half = lconst(T, inv(cfromQ(C, Q(2))), j)
    Av, Bv = (v + sv) * half, (v - sv) * lconst(T, inv(I + I), j)
    (iszero(Av) || iszero(Bv)) && return nothing
    # Laurent coefficients a_k (k = -K … ) of a σ-invariant X = N/θ^K, as real constants
    function nonvanishing(X)
        degree(X.den) == length(X.den.c) - 1 && all(iszero, X.den.c[1:(end - 1)]) || return false
        K = degree(X.den)
        a = [const_value(T, c) for c in X.num.c]
        any(isnothing, a) && return false
        P = UPoly{C}
        ap, am = P(C[one(C), I]), P(C[one(C), -I])
        Ah = sum(scale(a[l + 1], ap^l * am^(2K - l)) for l in eachindex(a) .- 1)
        all(c -> iszero(im_part(c)), Ah.c) || return false
        Ar = UPoly{RT}(RT[re_part(c) for c in Ah.c])
        Aπ = sum(re_part(a[l + 1]) * (iseven(l - K) ? 1 : -1) for l in eachindex(a) .- 1)
        !iszero(Aπ) && real_root_count(Ar, nothing, nothing, c -> Int(real_sign(c))) == 0
    end
    out = Any[]
    s != 0 && push!(out, (cfromQ(C, Q(s)), :lin, uel, uterm))
    # printed as real_term(B)/real_term(A): each is σ-invariant (no conjugate denominator to multiply in)
    ratio(X, Y) = b -> mk(b, :/, real_term(b, T, kinds, X, j), real_term(b, T, kinds, Y, j))
    if nonvanishing(Av)
        push!(out, (one(C), :atan, Bv / Av, ratio(Bv, Av)))
    elseif nonvanishing(Bv)
        push!(out, (-one(C), :atan, Av / Bv, ratio(Av, Bv)))
    else
        return nothing
    end
    out
end

# Re(c log w) as real pieces (coefficient, :log | :atan | :lin, argument[, printer]), see above
function real_log_pieces(T::Tower, kinds, c, w)
    C = ctype(T)
    j = levelof(T, w)
    sw = tconj(T, kinds, w, j)
    sc = cconj_g(T.consts, c)
    half = inv(cfromQ(C, Q(2)))
    I = cimag(C)
    cr = (c + sc) * half
    ci = (c - sc) * inv(I + I)
    pieces = Any[]
    if sw == w
        iszero(cr) || push!(pieces, (cr, :log, w))
        return pieces
    end
    iszero(cr) || push!(pieces, (cr * half, :log, w * sw))
    U = (w + sw) * lconst(T, half, j)
    V = (w - sw) * lconst(T, inv(I + I), j)
    if !(iszero(ci) || iszero(U) || iszero(V))
        cp = continuous_arg_pieces(T, kinds, j, w)      # -Im c · arg w, continuous (step TC)
        if cp !== nothing
            for pc in cp                                # (factor, kind, argument[, printer])
                push!(pieces, (-ci * pc[1], pc[2:end]...))
            end
            return pieces
        end
    end
    if !(iszero(ci) || iszero(U) || iszero(V))          # U = 0: w/σw = -1, constant
        a = V / U
        # at the base, atan(V/U) with V constant has a pole where U = 0; -atan(U/V) has the same
        # derivative and is continuous there (e.g. atan(1/t) -> -atan(t))
        if j == 0 && degree(a.num) <= 0 && degree(a.den) > 0
            push!(pieces, (ci, :atan, inv(a)))
        else
            push!(pieces, (-ci, :atan, a))
        end
    end
    pieces
end

# combine real pieces with the same argument (atan(-u) = -atan(u)); zero coefficients dropped
function merge_pieces(pieces)
    out = Any[]
    for pc in pieces
        c, k, a = pc[1], pc[2], pc[3]
        i = findfirst(p -> p[2] === k && p[3] == a, out)
        if i !== nothing
            out[i] = (out[i][1] + c, out[i][2:end]...)
            continue
        end
        i = k === :atan ? findfirst(p -> p[2] === :atan && p[3] == -a, out) : nothing
        if i !== nothing
            out[i] = (out[i][1] - c, out[i][2:end]...)
            continue
        end
        push!(out, pc)
    end
    filter(p -> !iszero(p[1]), out)
end

# the real form of an integral over ℚ(i) as a term, verified: D(real form) == f in T
function to_term_real(b::Builder, T::Tower, L::Int, res::ElemIntegral, f; pos = nothing)
    kinds = sigma_kinds(T)
    C = ctype(T)
    v = liftto(T, res.v, L)
    vr = (v + tconj(T, kinds, v, L)) * lconst(T, inv(cfromQ(C, Q(2))), L)
    # (with ≥ CHECK_IMAGE_DEPTH parameters, D vr is checked at images of them at the end, step CK)
    img = fdepth(C) >= CHECK_IMAGE_DEPTH
    tot = img ? zero(v) : D(T, L, vr)
    ts = Any[]
    iszero(vr) || push!(ts, real_term(b, T, kinds, vr, L))
    function emit!(TT, kk, pieces)              # push the terms, return Σ derivatives (in TT)
        ds = zero(TT.Ts[L + 1])
        for pc in pieces
            coef, kind, arg = pc[1], pc[2], pc[3]
            a = liftto(TT, arg, L)
            da = kind === :log ? D(TT, L, a) / a : kind === :lin ? D(TT, L, a) : D(TT, L, a) / (one(a) + a * a)
            ds = ds + lconst(TT, coef, L) * da
            at = length(pc) >= 4 ? pc[4](b) : real_term(b, TT, kk, arg)
            t = kind === :lin ? at : mk(b, kind, at)
            push!(ts, isone(coef) ? t : mk(b, :*, cterm(b, coef), t))
        end
        ds
    end
    pieces = Any[]
    for (c, w) in res.logs
        append!(pieces, real_log_pieces(T, kinds, c, w))
    end
    pieces = merge_pieces(pieces)
    pos === nothing || (pieces = real_log_signs(T, pieces, pos))   # step EC: real log arguments
    tot = tot + emit!(T, kinds, pieces)
    isempty(res.atans) || throw(RischError("unexpected atan terms over ℚ(i)"))
    merged = Any[]                                      # (fn, w, coefficient): like terms added
    for q in res.quads
        q isa SpecialTerm || continue
        d = liftto(T, q.deriv, L)                       # Re of the term differentiates to (d + σd)/2
        tot = tot + (d + tconj(T, kinds, d, L)) * lconst(T, inv(cfromQ(C, Q(2))), L)
        parts = special_parts_real(T, kinds, q)
        if parts === nothing
            push!(ts, special_out_real(b, T, kinds, q))
            continue
        end
        for (fn, w, pr, qa, ca, cb) in parts
            j = findfirst(m -> m[1] === fn && m[3] == pr && m[4] == qa && levelof(T, m[2]) == levelof(T, w) && m[2] == w, merged)
            j === nothing ? push!(merged, Any[fn, w, pr, qa, ca, cb]) : (merged[j][5] += ca; merged[j][6] += cb)
        end
    end
    for (fn, w, pr, qa, ca, cb) in merged                # e^pr (a cos q + b sin q) fn(w)
        cs = Any[]
        if iszero(qa)
            iszero(ca) || push!(cs, isone(ca) ? nothing : cterm(b, ca))
        else
            sc(c, t) = isone(c) ? t : mk(b, :*, cterm(b, c), t)
            iszero(ca) || push!(cs, sc(ca, mk(b, :cos, cterm(b, qa))))
            iszero(cb) || push!(cs, sc(cb, mk(b, :sin, cterm(b, qa))))
        end
        isempty(cs) && continue
        t = mk(b, fn, real_term(b, T, kinds, w))
        k = length(cs) == 1 ? cs[1] : mk(b, :+, cs...)
        iszero(pr) || (k = k === nothing ? mk(b, :exp, cterm(b, pr)) : mk(b, :*, mk(b, :exp, cterm(b, pr)), k))
        push!(ts, k === nothing ? t : mk(b, :*, k, t))
    end
    for q in res.quads
        q isa SpecialTerm && continue
        q isa ExtQuadPair || throw(RischError("unexpected term $(typeof(q)) over ℚ(i)"))
        T2 = q.T2
        k2 = sigma_kinds(T2)
        a2, W2 = galois_d(q.a), change_constants(T2, T2, q.W, galois_d)
        ds = emit!(T2, k2, merge_pieces(vcat(real_log_pieces(T2, k2, q.a, q.W),
                                             real_log_pieces(T2, k2, a2, W2))))
        tot = tot + change_constants(T2, T, ds, qs_down)
    end
    ok = img ? check_D_images(T, L, vr, liftto(T, f, L) - tot) : nothing
    ok === nothing && (ok = (img ? tot + D(T, L, vr) : tot) == liftto(T, f, L))
    ok || throw(RischError("internal check failed: the real form of the antiderivative does not differentiate back"))
    isempty(ts) && return b.lift(0)
    length(ts) == 1 ? ts[1] : mk(b, :+, ts...)
end
