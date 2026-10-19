# ---------------------------------------------------------------------------
# Step 10d: two radicands, square roots of linear polynomials u₁ = a x + b, u₂ = c x + d
#
# y = √u₁ gives x = (y² - b)/a and u₂ = (c/a) y² + d - c b/a, a quadratic in y without a
# linear term, so √u₂ = R is the 10b/10c case in the variable y: y = φ₂(t), R = ψ₂(t) over S.
# Then x = (φ₂(t)² - b)/a, u₁^(k/2) = φ₂(t)^k, u₂^(k/2) = ψ₂(t)^k (the curve y² = u₁, R² = u₂
# is a conic). Both orders of the radicands are tried. Radicands of higher degree, other
# indices, or three or more radicands give curves of genus ≥ 1 in general: refused.
# ---------------------------------------------------------------------------
function integrate_two_radicals(f, xk::String, groups, b0::Builder, verify::Bool, cfix = nothing, pmap = nothing)
    linear(u) = isone(u.den) && degree(u.num) == 1
    all(g -> g[3] == 2 && linear(g[1]), groups) || throw(RischNotImplemented(
        "radicals of two different radicands: only square roots of two linear polynomials are supported"))
    cands = Any[]
    for (g1, g2) in (groups, reverse(groups))
        u1, t1, _ = g1
        u2, t2, _ = g2
        b, a = u1.num.c
        d, c = u2.num.c
        by = Builder(b0.build, b0.lift, mk(b0, :sqrt, t1))   # the variable y = √u₁
        eus = try
            euler_substitution(c / a, Q(0), d - c * b / a, by, t2; pref = cfix_d(cfix))
        catch e
            e isa RischNotImplemented || rethrow()
            continue                                    # √u₂ never real where u₁ ≥ 0
        end
        for (S, φ2, ψ2, tterm) in eus
            kS = q -> frac(UPoly{S}(S[cfromQ(S, q)]))
            φ = (φ2 * φ2 - kS(b)) * kS(inv(a))
            radval = function (ue, e)
                k = 2 * e
                isone(denominator(k)) || throw(RischError("radical exponent not a multiple of 1/2"))
                ue == u1 ? φ2^Int(numerator(k)) :
                ue == u2 ? ψ2^Int(numerator(k)) : throw(RischError("unexpected radicand"))
            end
            push!(cands, (S, φ, radval, tterm, real_pos(Any[φ2, ψ2])))   # √u₁, √u₂ > 0 (EL)
        end
    end
    isempty(cands) && throw(RischNotImplemented(
        "√($(groups[1][2])) and √($(groups[2][2])) are never real at the same point"))
    try_substitutions(f, xk, cands, b0, verify, cfix, pmap)
end

# Euler substitutions for R = √(A x² + B x + C): (S, φ, ψ, t-term) with x = φ(t), R = ψ(t),
# φ, ψ ∈ S(t) (identities for the principal root). Over S = ℚ (10b):
#   √A = s ∈ ℚ₊:    R = t - s x,        t = R + s x,        x = (t² - C)/(B + 2 s t)
#   √C = s ∈ ℚ₊:    R = x t + s,        t = (R - s)/x,      x = (2 s t - B)/(A - t²)
#   roots r₁ ≠ r₂:  R = t (x - r₁),     t = R/(x - r₁),     x = (A r₂ - r₁ t²)/(A - t²)
#   (r₁ chosen so that x - r₁ > 0 on the real domain: the smaller root when A < 0)
# Otherwise (10c) through a point (x₀, y₀) of the conic R² = Q(x), y₀ > 0, see `euler_point`:
# a small rational point (S = ℚ), else S = ℚ(i)(√d) with √A (A > 0, the point at infinity) or
# y₀ = √Q(x₀) (x₀ = 0 if C > 0, else the vertex). i is there for the atan terms (residues
# ±i·r); the answer is real (Step 7 real form, sqrt(d) kept symbolic).
# R: the term for √Q (default sqrt(uterm); √u/s for a radicand u = s²Q, step SQ)
function euler_substitution(A::Q, B::Q, C::Q, b::Builder, uterm; pref::Int = 1, R = nothing)
    P = UPoly{Q}
    t = frac(xpoly(Q))
    kq(c) = frac(P(Q[c]))
    R === nothing && (R = mk(b, :sqrt, uterm))
    sA = A > 0 ? rat_sqrt(A) : nothing
    if sA !== nothing
        φ = (t * t - kq(C)) / (kq(B) + kq(2 * sA) * t)
        ψ = t - kq(sA) * φ
        tterm = mk(b, :+, R, isone(sA) ? b.x : mk(b, :*, cterm(b, sA), b.x))
        return [(Q, φ, ψ, tterm)]
    end
    sC = C > 0 ? rat_sqrt(C) : nothing
    if sC !== nothing
        φ = (kq(2 * sC) * t - kq(B)) / (kq(A) - t * t)
        ψ = φ * t + kq(sC)
        tterm = mk(b, :/, mk(b, :+, R, cterm(b, -sC)), b.x)
        return [(Q, φ, ψ, tterm)]
    end
    rts = rational_roots(P(Q[C, B, A]))
    if length(rts) == 2
        r1, r2 = A < 0 ? (minimum(rts), maximum(rts)) : (maximum(rts), minimum(rts))
        φ = (kq(A * r2) - kq(r1) * t * t) / (kq(A) - t * t)
        ψ = t * (φ - kq(r1))
        xr = iszero(r1) ? b.x : mk(b, :+, b.x, cterm(b, -r1))
        return [(Q, φ, ψ, mk(b, :/, R, xr))]
    end
    Qv(x0) = (A * x0 + B) * x0 + C
    for h in 1:12, q in 1:h, p in (h - q, q - h)        # small rational points, by height
        gcd(p, q) == 1 || continue
        x0 = Q(p) // Q(q)
        y0 = rat_sqrt(Qv(x0))
        (y0 === nothing || iszero(y0)) && continue
        return [euler_point(Q, y0, A, B, x0, b, uterm, R)]
    end
    # over ℚ(i)(√d), several candidates (the constants the answer needs are not known in
    # advance, e.g. ∫ dx/(x √(2x² + 3)) needs √3, not √2): √A (A > 0), the point (0, √C)
    # (C > 0), the vertex (A < 0: the maximum of Q, positive if Q ever is)
    cands = Any[]
    if pref > 1                     # 10e: the constant field ℚ(i)(√pref) is fixed: a point with y₀ ∈ ℚ √pref
        for h in 1:12, q in 1:h, p in (h - q, q - h)
            gcd(p, q) == 1 || continue
            x0 = Q(p) // Q(q)
            (Qv(x0) > 0 && rat_sqrt(Qv(x0) / pref) !== nothing) || continue
            push!(cands, euler_point(qs_field(Qv(x0))..., A, B, x0, b, uterm, R))
            break
        end
    end
    if A > 0                                            # point at infinity: R = t - √A x
        S, s = qs_field(A)
        PS = UPoly{S}
        ts = frac(xpoly(S))
        kS = c -> frac(PS(S[c]))
        φ = (ts * ts - kS(cfromQ(S, C))) / (kS(cfromQ(S, B)) + kS(s + s) * ts)
        ψ = ts - kS(s) * φ
        push!(cands, (S, φ, ψ, mk(b, :+, R, mk(b, :*, cterm(b, s), b.x))))
    end
    for x0 in (Q(0), A < 0 ? -B / (2 * A) : nothing)
        (x0 === nothing || Qv(x0) <= 0) && continue
        any(c -> c[1] === Q, cands) && break
        y0 = rat_sqrt(Qv(x0))
        y0 === nothing ? push!(cands, euler_point(qs_field(Qv(x0))..., A, B, x0, b, uterm, R)) :
                         push!(cands, euler_point(Q, y0, A, B, x0, b, uterm, R))
    end
    isempty(cands) && throw(RischNotImplemented("√($uterm): the radicand is never positive: no real square root"))
    unique(c -> c[1], cands)                            # one candidate per constant field
end

# S = ℚ(i)(√d) and √v ∈ S for v ∈ ℚ₊ not a square (v = σ² d, d squarefree)
function qs_field(v::Q)
    σ, d = sqfree_split(numerator(v) * denominator(v))
    S = QSB{Int(d),QI}
    S, S(zero(QI), QI(Q(σ) // Q(denominator(v)), Q(0)))
end

# Euler substitution through the point (x₀, y₀) of R² = Q(x) (y₀ ∈ S, y₀ > 0):
# R = y₀ + t (x - x₀), t = (R - y₀)/(x - x₀); with h = x - x₀, Q(x) = y₀² + Q'(x₀) h + A h²
# gives h = (2 y₀ t - Q'(x₀))/(A - t²), x = x₀ + h, R = y₀ + t h.
function euler_point(::Type{S}, y0::S, A::Q, B::Q, x0::Q, b::Builder, uterm, R = mk(b, :sqrt, uterm)) where {S}
    PS = UPoly{S}
    t = frac(xpoly(S))
    kS(c) = frac(PS(S[c]))
    c(q::Q) = cfromQ(S, q)
    h = (kS(y0 + y0) * t - kS(c(2 * A * x0 + B))) / (kS(c(A)) - t * t)
    φ = kS(c(x0)) + h
    ψ = kS(y0) + t * h
    xr = iszero(x0) ? b.x : mk(b, :+, b.x, cterm(b, -x0))
    S, φ, ψ, mk(b, :/, mk(b, :+, R, cterm(b, -y0)), xr)
end
