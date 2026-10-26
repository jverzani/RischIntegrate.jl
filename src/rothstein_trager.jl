# ---------------------------------------------------------------------------
# Rothstein–Trager log part for R/D, D squarefree monic, deg R < deg D, over ℚ
# ---------------------------------------------------------------------------
# Stage 5a: terms with quadratic-irrational constants (residues in ℚ(√d), d squarefree)
struct QuadLog                  # β√d · log((U + √d V)/(U - √d V)),  d > 1
    β::Q
    d::Int
    U::CX
    V::CX
    sq::Bool                    # printed as (β√d/2) log(ratio²) = β√d log|ratio| (step EC)
end
QuadLog(β, d, U, V) = QuadLog(β, d, U, V, false)
struct QuadAtan                 # c√e · atan(√e u)  (inverted = false)  or  c√e · atan(u/√e)  (true)
    c::Q
    e::Int
    u::CXF
    inverted::Bool
end

struct RationalIntegral{C}
    rational::Frac{UPoly{C}}               # rational (non-log) part
    logs::Vector{Tuple{C,UPoly{C}}}        # c * log(w)
    atans::Vector{Tuple{C,Frac{UPoly{C}}}} # c * atan(u)
    unresolved::Vector{Any}                # (residue polynomial, R, D) not handled yet
    quads::Vector{Any}                     # QuadLog / QuadAtan (C = ℚ only)
end
RationalIntegral(r, l, a, u) = RationalIntegral(r, l, a, u, Any[])

# Residues are the two roots a = α ± β√d of the irreducible quadratic `rest`. With
# W = gcd(D, A - a D') = U + √d V:   a log W + ā log W̄ is
#   α log(U² - d V²) + β√d log((U + √d V)/(U - √d V))                 (d > 1)
#   α log(U² + e V²) + β√e LogToAtan(U, √e V),   e = -d               (d < 0)
function quad_terms(A::CX, D::CX, dD::CX, rest::CX)
    rest = monic(rest)
    p0, p1 = rest.c[1], rest.c[2]
    α = -p1 / 2
    Δ = p1^2 - 4 * p0
    iszero(Δ) && return nothing
    s, d = sqfree_split(numerator(Δ) * denominator(Δ))
    (d == 1 || abs(d) > 10^9) && return nothing
    β = Q(s) / (2 * denominator(Δ))
    dd = Int(d)
    S = QS{dd}
    a = S(α, β)
    W = gcd(toQS(S, D), toQS(S, A) - scale(a, toQS(S, dD)))
    degree(W) > 0 || return nothing
    U = CX(Q[w.a for w in W.c])
    V = CX(Q[w.b for w in W.c])
    logs = Tuple{Q,CX}[]
    quads = Any[]
    iszero(α) || push!(logs, (α, U * U - dd * (V * V)))
    if !iszero(V)
        if dd > 0
            push!(quads, QuadLog(β, dd, U, V))
        elseif !iszero(U)
            # W = U + i√e V: β√e LogToAtan(U, √e V) = Σ 2β√e atan(√e uⱼ)
            e = -dd
            for u in log_to_atan_sqrt(U, V, Q(e))
                push!(quads, QuadAtan(2 * β, e, frac(u), false))
            end
        end
    end
    logs, quads
end

# log and atan terms for one irreducible quadratic residue factor q over ℚ; false if not handled.
# Residues α ± βi (β rational): with W = gcd(D, A - (α + βi) D') = U + iV,
#   α log(U² + V²) + β LogToAtan(U, V)  (atans of polynomials);  otherwise `quad_terms` (Stage 5a).
function quad_factor!(logs, atans, quads, A::CX, D::CX, dD::CX, q::CX)
    q = monic(q)
    p0, p1 = q.c[1], q.c[2]
    α = -p1 / 2
    s = rat_sqrt(-(p1^2 - 4 * p0))          # sqrt(-discriminant), only if rational
    if s !== nothing && !iszero(s)
        β = s / 2
        a = QI(α, β)
        W = gcd(toQI(D), toQI(A) - scale(a, toQI(dD)))
        U = CX(C[w.re for w in W.c])
        V = CX(C[w.im for w in W.c])
        iszero(α) || push!(logs, (α, U * U + V * V))
        if !iszero(U) && !iszero(V)
            for p in log_to_atan(U, V)              # β LogToAtan(U, V) ≡ 2β atan(U/V)
                push!(atans, (2 * β, frac(p)))
            end
        end
        return true
    end
    qt = quad_terms(A, D, dD, q)            # irrational or non-square complex residues (5a)
    qt === nothing && return false
    append!(logs, qt[1])
    append!(quads, qt[2])
    true
end

# an element of ℚ(√d)(x) that lies in ℚ(x) (normal form: then every coefficient is rational)
function qs_down(f::Frac{UPoly{QSB{d,Q}}}) where {d}
    down(p) = all(c -> iszero(c.b), p.c) ? CX(Q[c.a for c in p.c]) :
              throw(RischError("real form of a RootSum: derivative not in ℚ(x)"))
    frac(down(f.num), down(f.den))
end

# Step SD. Over C = B(t) (t the outermost constant generator: e, log 2, …), the factor of D that does
# not involve t: clear the denominators of D's coefficients and write D = Σ_k t^k E_k(s), E_k ∈ B[s];
# G = gcd_k E_k. Returns G (as a polynomial over C) when 0 < deg G < deg D, else nothing.
function tfree_factor(D::UPoly{Frac{UPoly{B}}}) where {B}
    C = Frac{UPoly{B}}
    PB = UPoly{B}
    L = reduce((a, b) -> quo(a * b, gcd(a, b)), (c.den for c in D.c if !iszero(c)); init = one(PB))
    Dh = PB[iszero(c) ? zero(PB) : c.num * quo(L, c.den) for c in D.c]   # coefficients in B[t]
    kmax = maximum(degree(p) for p in Dh)
    G = zero(PB)
    for k in 0:kmax
        Ek = PB(B[k < length(p.c) ? p.c[k + 1] : zero(B) for p in Dh])
        iszero(Ek) || (G = iszero(G) ? monic(Ek) : gcd(G, Ek))
    end
    (0 < degree(G) < degree(D)) || return nothing
    UPoly{C}(C[kconst(c) for c in G.c])
end
tfree_factor(D::UPoly) = nothing

# Step SY: a quadratic residue factor over C = ℚ(t₁, …) (parameters, e, log p) with roots α ± iβ,
# α, β ∈ C (-Δ a square in C): as `quad_factor!`, over the complex field ℚ(i)(t₁, …): W = U + iV with
# U = (W + W̄)/2, V = (W - W̄)/(2i) (conjugation acts on the coefficients; the generators are real),
# α log(U² + V²) + β LogToAtan(U, V). false if not of this kind (then RootSum).
cplx_type(::Type{Q}) = QI
cplx_type(::Type{Frac{UPoly{B}}}) where {B} = Frac{UPoly{cplx_type(B)}}
function quad_factor_t!(logs, atans, A::UPoly{C}, D::UPoly{C}, dD::UPoly{C}, q::UPoly{C}) where {C}
    q = monic(q)
    p0, p1 = q.c[1], q.c[2]
    two = cfromQ(C, Q(2))
    α = -p1 / two
    s = csqrt(-(p1 * p1 - 2 * two * p0))
    (s === nothing || iszero(s)) && return false
    β = s / two
    CC = cplx_type(C)
    I = cimag(CC)
    up(p) = UPoly{CC}(CC[to_complex(CC, c) for c in p.c])
    a = to_complex(CC, α) + I * to_complex(CC, β)
    W = gcd(up(D), up(A) - scale(a, up(dD)))
    degree(W) > 0 || return false
    h = inv(cfromQ(CC, Q(2)))
    Uc = [to_real((w + cconj(w)) * h) for w in W.c]
    Vc = [to_real((w - cconj(w)) * inv(I + I)) for w in W.c]
    (any(isnothing, Uc) || any(isnothing, Vc)) && return false
    U, V = UPoly{C}(C[Uc...]), UPoly{C}(C[Vc...])
    iszero(α) || push!(logs, (α, U * U + V * V))
    if !iszero(U) && !iszero(V)
        for p in log_to_atan(U, V)
            push!(atans, (2 * β, frac(p)))
        end
    end
    true
end

function log_part(A::UPoly{C}, D::UPoly{C}) where {C}
    if rational_tfield(C) && !iszero(A)
        G = tfree_factor(D)
        if G !== nothing                       # A/D = A₁/G + A₂/H: separate residue polynomials (SD)
            H, r = divrem(D, G)
            iszero(r) || throw(RischError("tfree_factor: G does not divide D"))
            sH, uG, g = gcdex(H, G)            # sH·H + uG·G = 1 (D squarefree: G, H coprime)
            isone(g) || throw(RischError("tfree_factor: G and D/G are not coprime"))
            p1 = log_part(rem(A * sH, G), G)
            p2 = log_part(rem(A * uG, H), monic(H))
            return vcat(p1[1], p2[1]), vcat(p1[2], p2[2]), vcat(p1[3], p2[3]), vcat(p1[4], p2[4])
        end
    end
    # D ∈ ℚ[x] over a parameter field: split by its factors over ℚ, so that each residue polynomial has
    # degree of a factor (a rational root gives its residue at once; a resultant over ℚ(a, b, …) of the
    # whole D would have roots it cannot find)
    if C <: Frac && !iszero(A) && degree(D) >= 2
        qs = [crational(c) for c in D.c]
        if all(!isnothing, qs)
            fs = factor_Q(UPoly{Q}(Q[q for q in qs]))
            if length(fs) > 1
                G = UPoly{C}(C[cfromQ(C, c) for c in fs[1].c])
                H, r = divrem(D, G)
                iszero(r) || throw(RischError("log_part: a factor over ℚ does not divide D"))
                sH, uG, g = gcdex(H, G)
                isone(g) || throw(RischError("log_part: factors over ℚ are not coprime"))
                p1 = log_part(rem(A * sH, G), G)
                p2 = log_part(rem(A * uG, H), monic(H))
                return vcat(p1[1], p2[1]), vcat(p1[2], p2[2]), vcat(p1[3], p2[3]), vcat(p1[4], p2[4])
            end
        end
    end
    CXl = UPoly{C}
    CXFl = Frac{UPoly{C}}
    logs = Tuple{C,CXl}[]
    atans = Tuple{C,CXFl}[]
    unresolved = Any[]
    quads = Any[]
    iszero(A) && return logs, atans, unresolved, quads
    dD = deriv(D)
    # (the resultant over more than MAX_ROOTSUM_GENS parameters does not finish for a quartic)
    C <: Frac && cdepth(C) > MAX_ROOTSUM_GENS && degree(D) > 2 && throw(RischNotImplemented(
        "residues of a denominator of degree $(degree(D)) over more than $MAX_ROOTSUM_GENS symbolic constants"))
    Rz = residue_resultant(D, A, dD)                 # R(z) = res_x(D, A - z D')
    iszero(Rz) && throw(RischError("zero resultant in the residue computation"))
    degree(Rz) <= 0 && return logs, atans, unresolved, quads
    Rsf = quo(Rz, gcd(Rz, deriv(Rz)))        # distinct residues
    roots = constant_roots(Rsf)
    rest = Rsf
    for a in roots
        W = gcd(D, A - scale(a, dD))
        degree(W) > 0 && !iszero(a) && push!(logs, (a, W))       # (a residue 0 adds no log)
        rest = quo(rest, CXl(C[-a, one(C)]))
    end
    degree(rest) == 0 && return logs, atans, unresolved, quads
    hard = rest                              # residue factors left for RootSum
    if C === Q                               # quadratic factors over ℚ: logs and atans (steps 5/5b)
        hard = one(CXl)
        for q in (degree(rest) > 2 ? factor_Q(rest) : [rest])
            degree(q) == 2 && quad_factor!(logs, atans, quads, A, D, dD, q) && continue
            degree(q) == 4 && quartic_real!(quads, A, D, dD, q) && continue
            hard = hard * q
        end
    end
    if rational_tfield(C) && degree(rest) == 2 && quad_factor_t!(logs, atans, A, D, dD, rest)   # step SY
        hard = one(CXl)
    end
    if degree(hard) > 0 && C === Q                  # even quartic factors with nested real forms (step BQ4)
        bq = biquad_log_part(A, D)
        bq === nothing || return bq
    end
    degree(hard) > 0 && push!(unresolved, (hard, A, D))
    logs, atans, unresolved, quads
end

function integrate_rational(f::Frac{UPoly{C}}) where {C}
    iszero(f) && return RationalIntegral(zero(typeof(f)), Tuple{C,UPoly{C}}[],
                                         Tuple{C,Frac{UPoly{C}}}[], Any[])
    g, Qp, R, Dsf = hermite_reduce(dx, f.num, f.den)
    rational = g + frac(integrate_poly(Qp))
    logs, atans, unresolved, quads = log_part(R, Dsf)
    RationalIntegral(rational, logs, atans, unresolved, quads)
end

# d/dx of the computed antiderivative, in ℚ(x) (for self-verification)
function derivative_of(res::RationalIntegral{C}) where {C}
    F = typeof(res.rational)
    tot = dx(res.rational)
    for (c, w) in res.logs
        tot = tot + kconst(c) * frac(deriv(w), w)
    end
    for (c, u) in res.atans
        tot = tot + kconst(c) * dx(u) / (one(F) + u * u)
    end
    for q in res.quads
        if q isa RationalIntegral || q isa QuarticNested   # real form of a quartic RootSum (R2, NR)
            tot = tot + qs_down(derivative_of(q))
        elseif q isa BiquadTerm                             # even quartic (BQ4)
            tot = tot + derivative_of(q)
        elseif q isa QuadLog  # d/dx [β√d log(W/W̄)] = 2βd (V'U - U'V)/(U² - dV²)
            U, V = q.U, q.V
            tot = tot + kconst(2 * q.β * q.d) * frac(deriv(V) * U - deriv(U) * V, U * U - q.d * (V * V))
        else                  # c√e atan(√e u):  c e u'/(1 + e u²);  c√e atan(u/√e):  c e u'/(e + u²)
            u, e = q.u, Q(q.e)
            den = q.inverted ? kconst(e) + u * u : one(F) + kconst(e) * u * u
            tot = tot + kconst(q.c * e) * dx(u) / den
        end
    end
    tot
end
check_result(res::RationalIntegral, f::Frac) = isempty(res.unresolved) && derivative_of(res) == f
