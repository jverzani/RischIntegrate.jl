# the real field of C: ℚ(i) -> ℚ, ℚ(i)(t₁, …) -> ℚ(t₁, …) (real generators e^a, log p)
real_ctype(::Type{QI}) = Q
real_ctype(::Type{Frac{UPoly{B}}}) where {B} = Frac{UPoly{real_ctype(B)}}
# c ∈ C with real coefficients (normal form is unique, so a real constant has them) in the real
# field, or nothing
to_real(c::QI) = iszero(c.im) ? c.re : nothing
function to_real(c::Frac{UPoly{B}}) where {B}
    RB = real_ctype(B)
    n, d = [to_real(a) for a in c.num.c], [to_real(a) for a in c.den.c]
    (any(isnothing, n) || any(isnothing, d)) && return nothing
    Frac{UPoly{RB}}(UPoly{RB}(RB[n...]), UPoly{RB}(RB[d...]))
end
to_complex(::Type{Frac{UPoly{B}}}, r::Frac) where {B} =
    Frac{UPoly{B}}(UPoly{B}(B[to_complex(B, a) for a in r.num.c]), UPoly{B}(B[to_complex(B, a) for a in r.den.c]))

# sign of a real constant: exact over ℚ; over ℚ(t₁, …) from a 256-bit evaluation of the generators
# (e^a, log p), and nothing (undecided) if the value is within 1e-40 of 0. Only used to choose a
# form (no pole in range, sign of a log argument), never for the answer itself. (`cdepth`: Step 6.)
cbig(c::Q, gens) = BigFloat(c)
function cbig(c::Frac{UPoly{B}}, gens) where {B}
    g = gens[cdepth(typeof(c))]
    t = g.kind === :exp ? exp(BigFloat(g.arg)) : log(BigFloat(g.arg))
    pe(p) = foldr((a, acc) -> acc * t + cbig(a, gens), p.c; init = BigFloat(0))
    pe(c.num) / pe(c.den)
end
csign(c::Q, gens) = Int(sign(c))
function csign(c, gens)
    iszero(c) && return 0
    any(g -> g.kind in (:sym, :symlog), gens) && return nothing     # a parameter: no sign (step SY)
    v = setprecision(() -> cbig(c, gens), BigFloat, 256)
    abs(v) < big(10)^-40 ? nothing : Int(sign(v))
end

# number of distinct real roots of p ∈ R[s] in [a, b] (a = nothing: -∞, b = nothing: +∞), Sturm;
# sg is the sign function of the real field R (nothing: undecided, then the result is nothing)
function real_root_count(p::UPoly{R}, a, b, sg = c -> Int(sign(c))) where {R}
    degree(p) <= 0 && return 0
    p = quo(p, gcd(p, deriv(p)))
    seq = UPoly{R}[p, deriv(p)]
    while degree(seq[end]) > 0
        r = -rem(seq[end - 1], seq[end])
        iszero(r) && break
        push!(seq, r)
    end
    at(q, x) = peval(q, cfromQ(R, Q(x)))
    sgn(q, x) = x === nothing ? sg(lc(q)) : sg(at(q, x))
    sgninf(q, side) = (s = sg(lc(q)); s === nothing ? nothing : side < 0 && isodd(degree(q)) ? -s : s)
    function changes(vals)
        any(isnothing, vals) && return nothing
        v = filter(!iszero, vals)
        count(k -> v[k] != v[k + 1], 1:(length(v) - 1))
    end
    va = changes([a === nothing ? sgninf(q, -1) : sgn(q, a) for q in seq])
    vb = changes([b === nothing ? sgninf(q, 1) : sgn(q, b) for q in seq])
    (va === nothing || vb === nothing) && return nothing
    va - vb + ((a !== nothing && iszero(at(p, a))) ? 1 : 0)     # roots in (a, b], plus a
end

# the signs w takes on {t ∈ ℝ : φ(t) > 0 for all φ ∈ pos}, exactly: one rational point in each
# open interval between consecutive real roots of w and of the numerators and denominators.
# R = ℚ or ℚ(√d) (real coefficients, step EC)
function signs_on(pos, w::UPoly{R}) where {R}
    Ps = UPoly{R}[φ.num * φ.den for φ in pos]          # the sign of φ where it is defined
    sg(c) = Int(real_sign(c))
    at(p, s) = peval(p, cfromQ(R, s))
    S = Set{Int}()
    for s in cell_points(prod(Ps; init = one(UPoly{R})) * w)
        all(P -> sg(at(P, s)) > 0, Ps) && push!(S, sg(at(w, s)))
    end
    S
end

# a rational bound for |c|
abs_bound(c::Q) = abs(c)
abs_bound(c::QS{d}) where {d} = abs(c.a) + abs(c.b) * (isqrt(d) + 1)

# rational points, one in each open interval between consecutive real roots of p (and one on each
# side of them): roots isolated by Sturm counts (`real_root_count`) and bisection
function cell_points(p::UPoly{R}) where {R}
    degree(p) <= 0 && return Q[0]
    p = quo(p, gcd(p, deriv(p)))
    sg(c) = Int(real_sign(c))
    at(s) = peval(p, cfromQ(R, s))
    B = 1 + maximum(abs_bound(c) for c in p.c) / abs_bound_low(lc(p))   # Cauchy: real roots in (-B, B)
    cnt(a, b) = real_root_count(p, a, b, sg) - (iszero(at(a)) ? 1 : 0)   # roots in (a, b]
    ivs = Tuple{Q,Q}[]
    stack = [(-B, B)]
    while !isempty(stack)
        a, b = pop!(stack)
        k = cnt(a, b)
        k == 0 && continue
        k == 1 && (push!(ivs, (a, b)); continue)
        m = (a + b) / 2
        push!(stack, (a, m), (m, b))
    end
    sort!(ivs)
    pts = Q[-B - 1]
    for k in 1:(length(ivs) - 1)
        (_, b1), (a2, b2) = ivs[k], ivs[k + 1]
        if !iszero(at(b1))
            push!(pts, b1)                              # root k < b1 ≤ a2 < root k+1
        elseif b1 < a2
            push!(pts, (b1 + a2) / 2)                   # (b1, a2] has no root
        else                                            # root k = b1 = a2: move right of it
            lo, hi = a2, b2
            while true
                m = (lo + hi) / 2
                cnt(lo, m) == 0 && (push!(pts, m); break)
                hi = m
            end
        end
    end
    push!(pts, B + 1)
    pts
end

# a positive rational lower bound for |c|, c ≠ 0 (exact for ℚ; a + b√d by refining √d)
abs_bound_low(c::Q) = abs(c)
function abs_bound_low(c::QS{d}) where {d}
    iszero(c.b) && return abs(c.a)
    iszero(c.a) && return abs(c.b) * isqrt(d)
    lo, hi = Q(isqrt(d)), Q(isqrt(d) + 1)               # lo ≤ √d ≤ hi, refined until |a + b r| > 0 on [lo, hi]
    while true
        v1, v2 = c.a + c.b * lo, c.a + c.b * hi
        sign(v1) == sign(v2) && !iszero(v1) && return min(abs(v1), abs(v2))
        m = (lo + hi) / 2
        m * m <= d ? (lo = m) : (hi = m)
    end
end
