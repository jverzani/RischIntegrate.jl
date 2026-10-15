# ---------------------------------------------------------------------------
# Stage 4: the Risch differential equation  y' + f y = g  over C(x)
#
# Used for  ∫ a θ^j  with θ = exp(u):  y' + (j u') y = a  (Bronstein ch. 6).
# Since f = j u' is a derivative it has no simple poles, which makes the bounds
# below sound (valuations at a finite place p, with f ~ p^-m, g ~ p^-k):
#   * m >= 2 : f y dominates y', so v(y) = v(g) + m: a pole of order k - m at most;
#   * f regular at p : y' dominates when y has a pole, so v(y) = v(g) + 1: order k - 1.
#   Hence y = N/D with D built from the poles of g only.
# At infinity (a = deg f, γ = deg g): a >= 0 gives deg y = γ - a, a <= -2 gives
# deg y <= max(γ + 1, 0). The numerator N is then a polynomial of known degree
# bound, found by exact linear algebra over C (the solution is unique because the
# homogeneous solution exp(-∫f) is not rational).
# Returns y ∈ C(x), or `nothing` if there is no rational solution.
# ---------------------------------------------------------------------------
function rde_base(f::Frac{UPoly{C}}, g::Frac{UPoly{C}}) where {C}
    P = UPoly{C}
    iszero(g) && return zero(Frac{P})
    iszero(f) && throw(RischError("RDE with f = 0 is plain integration"))
    Fn, Df = f.num, f.den
    G, Dg = g.num, g.den
    a = degree(Fn) - degree(Df)
    a == -1 && return :general                          # simple pole of f at infinity (step 9c)
    # denominator bound
    Dn = one(P)
    fparts = squarefree(Df)
    for (gk, k) in squarefree(Dg)
        remaining = gk
        for (fi, i) in fparts
            part = gcd(remaining, fi)
            degree(part) > 0 || continue
            i == 1 && return :general                   # simple pole of f (step 9c)
            Dn = Dn * part^max(0, k - i)
            remaining = quo(remaining, part)
        end
        Dn = Dn * remaining^max(0, k - 1)
    end
    any(i == 1 for (_, i) in fparts) && return :general # simple poles of f elsewhere: weak normalisation
    γ = degree(G) - degree(Dg)
    nup = a >= 0 ? γ - a : max(γ + 1, 0)
    M = nup + degree(Dn)
    M < 0 && return nothing
    dD = deriv(Dn)
    mono(k) = P(C[i == k + 1 ? one(C) : zero(C) for i in 1:(k + 1)])
    cols = P[]
    for k in 0:M
        N = mono(k)
        dN = k == 0 ? zero(P) : k * mono(k - 1)
        push!(cols, Df * Dg * (Dn * dN - dD * N) + Fn * Dg * Dn * N)
    end
    target = G * Df * Dn * Dn
    len = maximum(length(p.c) for p in [cols; target])
    coords(p) = C[i <= length(p.c) ? p.c[i] : zero(C) for i in 1:len]
    sol = solve_columns([coords(p) for p in cols], coords(target))
    sol === nothing && return nothing
    y = frac(P(sol), Dn)
    dx(y) + f * y == g || throw(RischError("RDE solution failed its own check"))
    y
end

# ---------------------------------------------------------------------------
# Stage 4b: the Risch differential equation over a tower K_m = k(t), k = K_{m-1}
#
#   y' + f y = g,   f = j u' (so exp(-∫f) = θ^-j is not in K by independence)
#
# Supported shape: f and g are polynomials in t (t = log), or Laurent polynomials
# in t (t = exp); a normal denominator raises RischNotImplemented. Writing
# y = Σ cᵢ tⁱ with cᵢ ∈ k:
#   t = log(w), t' = w'/w ∈ k:   cᵢ' + f cᵢ + (i+1) cᵢ₊₁ t' = gᵢ   (f ∈ k)
#   t = exp(w):                  cᵢ' + (f + i w') cᵢ = gᵢ          (f ∈ k)
# which are RDEs in k (recursion). If f itself involves t, the leading term of f
# fixes the support of y ( deg y = deg g - deg f ), and the cᵢ follow
# algebraically from the top (or from the bottom when only negative powers of an
# exponential occur). Every candidate is verified exactly; bounds only decide
# where to look, so they can lose a solution but never invent one.
# Returns y ∈ K_m or `nothing` when there is no solution.
# ---------------------------------------------------------------------------
function laurent_of(T::Tower, m::Int, h, polynomial::Bool)
    k = T.Ts[m]
    θ = xpoly(k)
    p = degree(h.den)
    ((isone(h.den)) || (!polynomial && h.den == θ^p)) || throw(RischNotImplemented(
        "the Risch differential equation over a tower with a normal denominator " *
        "(needs the full Bronstein ch. 6 denominator bound and SPDE reduction)"))
    d = Dict{Int,k}()
    for (idx, c) in enumerate(h.num.c)
        iszero(c) || (d[idx - 1 - p] = c)
    end
    d
end

function from_laurent(T::Tower, m::Int, c::Dict)
    k = T.Ts[m]
    P = UPoly{k}
    isempty(c) && return zero(T.Ts[m + 1])
    lo, hi = minimum(keys(c)), maximum(keys(c))
    p = max(0, -lo)
    coeffs = fill(zero(k), hi + p + 1)
    for (i, ci) in c
        coeffs[i + p + 1] = ci
    end
    frac(P(coeffs), xpoly(k)^p)
end

# y' = g in K_m, y ∈ K_m with no logarithms allowed (used when f vanishes)
function integrate_const(T::Tower, m::Int, g)
    r = try
        integrate_el(T, m, g)
    catch e
        e isa NotElementary ? nothing : rethrow()
    end
    (r === nothing || !isempty(r.logs) || !isempty(r.atans) || !isempty(r.quads)) ? nothing : r.v
end

function rde(T::Tower, m::Int, f, g)
    iszero(g) && return zero(T.Ts[m + 1])
    if m == 0
        r = rde_base(f, g)
        return r === :general ? rde_general(T, 0, f, g) : r
    end
    lv = T.levels[m]
    k = T.Ts[m]
    zk = zero(k)
    islog = lv.kind in (:log, :atan)                    # primitive (log or atan, step TA)
    # normal denominators (or a log-level fraction): the general solver (step 9a)
    (laurent_shape(T, m, f, islog) && laurent_shape(T, m, g, islog)) || return rde_general(T, m, f, g)
    fl = laurent_of(T, m, f, islog)
    gl = laurent_of(T, m, g, islog)
    isempty(fl) && throw(RischError("RDE with f = 0 is plain integration"))
    df, ef = maximum(keys(fl)), minimum(keys(fl))
    dg, eg = maximum(keys(gl)), minimum(keys(gl))
    c = Dict{Int,k}()
    undecided = false                                     # exp case: cancellation not decided (8b)
    if islog
        tp = lv.dtheta.c[1]
        if df == 0                                        # f ∈ k: triangular system of RDEs in k
            st = logderiv_solve(T, m - 1, fl[0])
            if st isa Tuple                               # f = z'/z: (z y)' = z g (step 9b)
                yp = prim_cancel(T, m, st[2], g.num, typemax(Int) ÷ 2)
                yp isa Symbol && cancellation_undecided()
                yp === nothing && return nothing
                return frac(yp)
            end
            for i in dg:-1:0
                rhs = get(gl, i, zk) - (i + 1) * get(c, i + 1, zk) * tp
                ci = rde(T, m - 1, fl[0], rhs)
                if ci === nothing
                    st === :unknown && cancellation_undecided()
                    return nothing
                end
                iszero(ci) || (c[i] = ci)
            end
        else                                              # deg y = deg g - deg f, algebraic
            hi = dg - df
            hi < 0 && return nothing
            for s in (hi + df):-1:df
                i = s - df
                rhs = get(gl, s, zk)
                for (a, fa) in fl
                    a == df || (rhs -= fa * get(c, s - a, zk))
                end
                rhs -= D(T, m - 1, get(c, s, zk)) + (s + 1) * get(c, s + 1, zk) * tp
                c[i] = rhs / fl[df]
            end
        end
    else
        wp = D(T, m - 1, lv.arg)                          # w' for t = exp(w)
        # Cancellation exponent (step 8b): where the lowest (f polynomial) or top (only
        # non-positive powers in f) equation reads c' + (f_0 + s w') c = g_s, a nonzero
        # homogeneous solution c ∈ k lets the support of y extend to s. `cancellation_exponent`
        # decides it completely when it can; `:unknown` means a failed search is not a proof.
        # (e.g. u = x + t, t = exp(x): s = -1 with c constant, ∫ exp(x + e^x) = θ/t;
        #  u = x + log x + t: s = -1 with c = 1/x, ∫ exp(x + log x + e^x)/x = θ/(x t))
        needs_s0 = (df > 0 && ef >= 0) || (df <= 0 && ef < 0)
        s0 = needs_s0 ? cancellation_exponent(T, m, get(fl, 0, zk), wp) : nothing
        undecided = s0 === :unknown
        i0 = s0 isa Int ? s0 : nothing
        if df == 0 && ef == 0                             # f ∈ k: decoupled RDEs in k
            for i in eg:dg
                gi = get(gl, i, zk)
                iszero(gi) && continue
                fi = fl[0] + i * wp
                ci = iszero(fi) ? integrate_const(T, m - 1, gi) : rde(T, m - 1, fi, gi)
                ci === nothing && return nothing
                c[i] = ci
            end
        elseif df > 0                                     # top-down
            hi = dg - df
            lo = min(eg, 0, eg - ef)
            i0 === nothing || (lo = min(lo, i0))
            if hi < lo
                undecided && cancellation_undecided()
                return nothing
            end
            for s in (hi + df):-1:(lo + df)
                i = s - df
                rhs = get(gl, s, zk)
                for (a, fa) in fl
                    a == df || (rhs -= fa * get(c, s - a, zk))
                end
                cs = get(c, s, zk)
                iszero(cs) || (rhs -= D(T, m - 1, cs) + s * wp * cs)
                c[i] = rhs / fl[df]
            end
        else                                              # only f_a with a <= 0, ef < 0: bottom-up
            lo = eg - ef
            hi = max(dg, 0)
            i0 === nothing || (hi = max(hi, i0))
            if hi < lo
                undecided && cancellation_undecided()
                return nothing
            end
            for s in (lo + ef):(hi + ef)
                i = s - ef
                rhs = get(gl, s, zk)
                for (a, fa) in fl
                    a == ef || (rhs -= fa * get(c, s - a, zk))
                end
                cs = get(c, s, zk)
                iszero(cs) || (rhs -= D(T, m - 1, cs) + s * wp * cs)
                c[i] = rhs / fl[ef]
            end
        end
    end
    filter!(p -> !iszero(p.second), c)
    y = from_laurent(T, m, c)
    D(T, m, y) + f * y == g && return y
    undecided && cancellation_undecided()
    nothing
end

laurent_shape(T::Tower, m::Int, h, polynomial::Bool) =
    isone(h.den) || (!polynomial && h.den == xpoly(T.Ts[m])^degree(h.den))
