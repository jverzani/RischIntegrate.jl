# ---------------------------------------------------------------------------
# SI2 phase 3b: the log part for one component θ. Written below for one radical, θ = yᵖ, y = b^(1/q)
# (b squarefree, gcd(p, q) = 1); the code works with any component θ = Π bₖ^rₖ through the integral basis
# ωⱼ of `KumCurve` (θᵠ = B, ωⱼ in place of y^(jp mod q), θ = ω₁).
#
# After Hermite reduction the integrand is h θ, h = (P + R/D)/b. With τ: y ↦ ζy (ζ = e^(2πi/q)),
# τ*θ = ζᵖθ, the residues over a root β of D are h(β) y(P)ᵖ: one orbit r·μ_q, and s = r^q ≡ hᵠ bᵖ
# mod the factor of D (at ∞, when ρ = pm/q ∈ ℤ, q | m, likewise). Supported: every s rational and in
# one class s = tᵠσ (σ q-th-power-free, the t of one sign); then L = ℚ(σ^(1/q)), and at each pole
# the place P_F with residue t_F σ^(1/q) has y ≡ S_F = (r/h)^p′ / b^((pp′-1)/q) mod F (pp′ ≡ 1 mod q).
# With b₀ = gcd of the t and n = t/b₀: look for v ∈ L[x, y] (polynomial, so no finite poles) with
#   div(v) = Σ N n_F P_F - o₁ (fiber at ∞) - (o₀ - o₁) P∞,₀,   o₀ - o₁ = -N n∞
# (Riemann–Roch: a space of dimension ≤ 1; linear conditions: v(x, Y_F) ≡ 0 mod F^(N n_F) with Y_F the
# q-th root of b lifted from S_F, and the Puiseux expansions at ∞). The yᵖ-component of d log v has
# the residues (1/q)·N n at the places of the orbits, so the log part is
#   λ (1/q) Σᵢ ζ^(-ip) log(τⁱ v),  λ = q b₀ σ^(1/q)/N,
# and its derivative is the yᵖ-component of λ v′/v, computed exactly in L(x)[y]/(yᵠ - b); the caller
# checks that what is left reduces to 0 (phase 3a). Output: a RootSum over αᵠ = 1 (α = ζ^(-ip)).
# ---------------------------------------------------------------------------

# s = tᵠ σ, σ an integer free of q-th powers (sign: in t for odd q, in σ for even q)
function kum_qclass(s::Q, q::Int)
    sg = sign(s)
    t, σ = Q(1), Q(sg < 0 && iseven(q) ? -1 : 1)
    for (num, isnum) in ((numerator(s), true), (denominator(s), false))
        for (pr, k) in factorint(big(abs(num)))
            σk = mod(k, q)
            tk = (k - σk) ÷ q
            if isnum
                t *= Q(pr)^tk
                σ *= Q(pr)^σk
            else                                        # 1/pr^k = pr^(q-σk)/pr^(q(tk+1))
                σk == 0 ? (t /= Q(pr)^tk) : (t /= Q(pr)^(tk + 1); σ *= Q(pr)^(q - σk))
            end
        end
    end
    (sg < 0 && isodd(q)) && (t = -t)
    t, Int(σ)
end

# y = b^(1/q) as a q-th root of b mod G, lifted from S (Newton)
function kum_root_lift(b::P, S::P, G::P, e::Int, q::Int) where {P<:UPoly}
    Y, k = S, 1
    qq = sum(one(P) for _ in 1:q)
    while k < e
        k = min(2k, e)
        Gk = G^k
        Y = rem(Y - (Y^q - b) * hyp_invmod(qq * Y^(q - 1), Gk), Gk)
    end
    Y
end

# A component θ = Π bₖ^rₖ (bₖ coprime squarefree, rₖ ∈ (0,1)), q = lcm of the denominators: θ^q = B,
# B = Π bₖ^(q rₖ). Integral basis ωⱼ = Π bₖ^{j rₖ} = θʲ/gⱼ, gⱼ = Π bₖ^⌊j rₖ⌋ (j = 0 … q-1), diagonal for
# τ: θ ↦ ζθ (ωⱼ ↦ ζʲωⱼ), θ = ω₁. At ∞ ωⱼ ~ wʲ/Π lcₖ^⌊j rₖ⌋ · x^ρⱼ (w the leading coefficient of θ,
# wᵠ = Π lcₖ^(q rₖ)), ρⱼ = Σ {j rₖ} deg bₖ. One base: ωⱼ = y^(jp mod q), the phase-3b setting above.
struct KumCurve
    bs::Vector{QX}
    rs::Vector{Q}
    q::Int
    es::Vector{Int}             # q rₖ
    B::QX
    A::QX
    ρ::Q
    fr::Vector{Vector{Q}}       # {j rₖ}
    fl::Vector{Vector{Int}}     # ⌊j rₖ⌋
    ρs::Vector{Q}
end
function KumCurve(bs::Vector{QX}, rs::Vector{Q})
    q = reduce(lcm, Int.(denominator.(rs)))
    es = [Int(r * q) for r in rs]
    B = prod((bs[k]^es[k] for k in eachindex(bs)); init = one(QX))
    A = prod(bs; init = one(QX))
    fr = [[mod(j * r, 1) for r in rs] for j in 0:(q - 1)]
    fl = [[Int(floor(j * r)) for r in rs] for j in 0:(q - 1)]
    ρs = [sum((fr[j + 1][k] * degree(bs[k]) for k in eachindex(bs)); init = Q(0)) for j in 0:(q - 1)]
    KumCurve(bs, rs, q, es, B, A, ρs[2], fr, fl, ρs)
end
# the series in 1/x of Π (bₖ/(lcₖ x^dₖ))^αₖ, coefficients 0 … N
function kum_series(C::KumCurve, αs, N::Int)
    s = [Q(1); zeros(Q, N)]
    for k in eachindex(C.bs)
        iszero(αs[k]) && continue
        sk = hyp_sqrt_series(C.bs[k], N, Q(αs[k]))
        s = [sum(s[i + 1] * sk[j - i + 1] for i in 0:j) for j in 0:N]
    end
    s
end
kum_lcprod(C::KumCurve, ex) = prod((lc(C.bs[k])^ex[k] for k in eachindex(C.bs)); init = Q(1))

# the log part (Wsub, [ScaledRootSum]) with d/dx(log part) = Wsub θ, or the exception to raise
kum_log_part(b::QX, p::Int, q::Int, P::QX, R::QX, D::QX, θterm, b0::Builder, xk::String; Nmax::Int = 8) =
    kum_log_part(KumCurve([b], [Q(p, q)]), P, R, D, θterm, b0, xk; Nmax = Nmax)
function kum_log_part(C::KumCurve, P::QX, R::QX, D::QX, θterm, b0::Builder, xk::String; Nmax::Int = 8)
    q, A = C.q, C.A
    ni(msg) = RischNotImplemented("∫ (…)·$θterm: $msg (SI2 phase 3b)")
    dD = deriv(D)
    # residue data: (F, s) at finite places (residue h θ, h = R/(A D′), s = hᵠ B); s∞ (with κ) at ∞
    fin = Tuple{QX,Q,QX}[]                              # (F, s, h mod F)
    if !iszero(R)
        for F in factor_Q(D)
            hF = rem(R * hyp_invmod(A * dD, F), F)
            sF = rem(hF^q * C.B, F)
            degree(sF) == 0 || return ni("residues of degree > q over ℚ")
            push!(fin, (F, sF.c[1], hF))
        end
    end
    κ = Q(0)
    if isone(denominator(C.ρ)) && !iszero(P)            # the x⁻¹ coefficient of P Π bₖ^(rₖ-1)
        N0 = degree(P) + 2
        sr = kum_series(C, C.rs .- 1, N0)
        e0 = Int(C.ρ) - degree(A)
        κ = sum((P.c[j + 1] * sr[j + e0 + 2] for j in 0:degree(P) if 0 <= j + e0 + 1 <= N0); init = Q(0))
    end
    # r∞ = -κ w/Π lcₖ, wᵠ = Π lcₖ^eₖ: s∞ = (-κ)ᵠ Π lcₖ^eₖ / Π lcₖ^q
    s∞ = iszero(κ) ? nothing : (-κ)^q * kum_lcprod(C, C.es) / kum_lcprod(C, fill(q, length(C.bs)))
    # several classes σ₁, σ₂, …: the residue spans σᵢ^(1/q)·ℚ(ζ_q) are independent when no σᵢ/σⱼ is a q-th
    # power in ℚ(ζ_q) (Kummer); then the integral is elementary iff each class's divisor is (torsion), and
    # the log parts add up
    groups = Dict{Int,Vector{Int}}()
    for (i, (_, sF, _)) in enumerate(fin)
        push!(get!(groups, kum_qclass(sF, q)[2], Int[]), i)
    end
    σ∞ = s∞ === nothing ? nothing : kum_qclass(s∞, q)[2]
    σ∞ === nothing || get!(groups, σ∞, Int[])
    isempty(groups) && return ni("no residues found")
    σs = sort!(collect(keys(groups)))
    for i in eachindex(σs), j in eachindex(σs)
        i < j || continue
        ρ = kum_qclass(Q(σs[i], σs[j]), q)[2]           # σᵢ/σⱼ modulo q-th powers
        (ρ != 1 && kum_cyclo_disjoint(ρ, q)) || return ni(
            "residues in the classes $(σs[i]) and $(σs[j]), which may be dependent over ℚ(ζ_$q)")
    end
    Wtot, rss = zero(QXF), Any[]
    for σc in σs
        r = kum_log_class(C, fin[groups[σc]], σc == σ∞ ? s∞ : nothing, κ, θterm, b0, xk; Nmax = Nmax)
        r isa Exception && return r
        Wtot = Wtot + r[1]
        push!(rss, r[2])
    end
    Wtot, rss
end

# the log part for the residues of one class (fin: the poles of the class; s∞: the residue at ∞ if it is
# in the class): (Wsub, ScaledRootSum) or the exception to raise
function kum_log_class(C::KumCurve, fin, s∞, κ::Q, θterm, b0::Builder, xk::String; Nmax::Int = 8)
    q = C.q
    ni(msg) = RischNotImplemented("∫ (…)·$θterm: $msg (SI2 phase 3b)")
    cls = [kum_qclass(s, q) for (_, s, _) in fin]
    s∞ === nothing || push!(cls, kum_qclass(s∞, q))
    isempty(cls) && return ni("no residues found")
    σ = cls[1][2]
    ts = [c[1] for c in cls]
    bb = reduce(gcd, abs.(ts)) * sign(ts[1])           # n = t/b₀ may be negative (full fibers make Δ effective)
    ns = [Int(t / bb) for t in ts]
    n∞ = s∞ === nothing ? 0 : ns[end]
    # L = ℚ(σ^(1/q)): ℚ[z]/(z^q - σ) when irreducible; else σ > 0 and the factor vanishing at the real
    # root (e.g. 4^(1/4) = √2)
    Mz = QX(vcat(Q[-σ], zeros(Q, q - 1), Q[1]))
    fsz = factor_Q(Mz)
    if length(fsz) > 1
        σ < 0 && return ni("residues in the class of $σ (z^$q - σ reducible, no real root)")
        rq = abs(Float64(σ))^(1 / q)
        Mz = argmin(f -> abs(foldr((c, acc) -> acc * rq + Float64(c), f.c; init = 0.0)), fsz)
    end
    run(f) = degree(Mz) == 1 ? f(Q, identity, -Mz.c[1]) : with_nf(Mz) do
        f(NFz, c -> cfromQ(NFz, c), nfz(xpoly(Q)))
    end
    # v = Σ cⱼ ωⱼ with div(v) = N·Δ, or (TG = (c_G, Θ)) N·T_G·Δ over L; λ = q b₀ σ^(1/q)/(N Θ)
    search(Ns, maxu; TG = nothing) = run() do K, emb, z
        PL = UPoly{K}
        cd, Sd, w = kum_lp_data(K, emb, z, C, fin, ts, ns, s∞, κ)
        for N in Ns
            sys = kum_orbit_system(K, emb, cd, Sd, w, C, n∞, N,
                                   TG === nothing ? [k == 0 ? 1 : 0 for k in 0:(q - 1)] : TG[1]; maxu = maxu)
            sys === nothing && continue
            sys === :toolarge && break
            unknowns, cols = sys
            ker = nullspace_cols(cols, length(cols))
            isempty(ker) && continue
            v = ker[1]
            cs = [zero(PL) for _ in 0:(q - 1)]
            for (i, (k, j)) in enumerate(unknowns)
                cs[k + 1] = cs[k + 1] + PL([i2 == j ? v[i] : zero(K) for i2 in 0:j])
            end
            # η = v′/v in L(x)⟨ω⟩: v′ = Σ (cⱼ′ + cⱼ Σₖ {j rₖ} bₖ′/bₖ) ωⱼ; ωᵢωⱼ = ω_{i+j mod q} · carry
            F_ = Frac{PL}
            dv = F_[frac(deriv(cs[jj + 1])) + frac(cs[jj + 1]) * kum_dlogω(K, emb, C, jj) for jj in 0:(q - 1)]
            mcols = Vector{F_}[]
            for jj in 0:(q - 1)                         # v·ω_jj
                col = [zero(F_) for _ in 1:q]
                for k in 0:(q - 1)
                    t, cr = kum_carry(K, emb, C, k, jj)
                    col[t + 1] = col[t + 1] + frac(cs[k + 1] * cr)
                end
                push!(mcols, col)
            end
            η = solve_columns(mcols, dv)
            η === nothing && throw(RischError("kum_log_part: v is not invertible"))
            λ = z * emb(Q(q) * bb / (N * (TG === nothing ? 1 : TG[2])))
            Wl = η[2] * frac(PL([λ]))                   # the θ = ω₁ component
            Wq = kum_down(Wl)
            Wq === nothing && return :notrational      # a principal N·Δ whose log part is not the one wanted
            return (N, cs, Wq)
        end
        nothing
    end
    found = search(1:Nmax, 800)
    found === :notrational && return ni("the logarithmic part found is not rational")
    if found === nothing && q > 2 && is_probable_prime(big(q))
        # q prime: the class of Δ (over L ∌ ζ) is torsion iff its χ-part is (its nontrivial isotypic parts are
        # conjugate, the trivial one comes from ℙ¹), i.e. iff the integral is elementary. Its order N₁ mod a
        # prime, a second prime where N₁Δ̄ is not principal, or N₁Δ not principal over L, prove it is not.
        ord = kum_lp_order(C, fin, ts, ns, s∞, κ, n∞, σ, Mz)
        ord === :infinite && return NotElementary(
            "∫ (…)·$θterm: the divisor of the residues has infinite order in the Jacobian of θ^$q = B " *
            "(its orders modulo two primes differ)")
        if ord isa Int                                  # the only possible order: one exact test
            found = search([ord], 5000)
            found === :notrational && return ni("the logarithmic part found is not rational")
            found === nothing && return NotElementary(
                "∫ (…)·$θterm: the divisor of the residues is not torsion (its order mod p would be $ord, " *
                "but $ord·Δ is not principal)")
        end
    elseif found === nothing && q > 2 && kum_cyclo_disjoint(σ, q)
        # q composite: only the parts of [Δ] with characters of exact order q matter. T = Π_{ℓ|q}(1 - τ^(q/ℓ))
        # kills the others and not these, which are conjugate (L ∩ ℚ(ζ_q) = ℚ); so does its Galois trace
        # T_G = Σ_a T(τ^a), which acts on them by Θ = Tr χ(T) ∈ ℚ. T_G is invariant under τ ↦ τ^a, so T_G·Δ
        # is defined over L and its conditions are rational (cyclotomic factors, Ramanujan sums): elementary
        # iff T_G·Δ is torsion, and then λ = q b₀ σ^(1/q)/(N Θ).
        # decided with T (small multiplicities): T·Δ of infinite order mod p proves it; if T·Δ is torsion of
        # order N_T, its conjugates T(τ^a)·Δ are too, so the order of T_G·Δ divides N_T: the exact tests at
        # the divisors of N_T construct the log part, or prove that T·Δ is not torsion
        cG = kum_TG(q)
        Θ = kum_Theta(cG, q)
        if !iszero(Θ)
            ord = kum_lp_order_T(C, fin, ts, ns, s∞, κ, n∞, σ, Mz)
            ord === :infinite && return NotElementary(
                "∫ (…)·$θterm: the order-$q part of the divisor of the residues has infinite order in the " *
                "Jacobian of θ^$q = B (its orders modulo two primes differ)")
            if ord isa Int
                for d in sort!(Int.(divisors(big(ord))))
                    found = search([d], 5000; TG = (cG, Θ))
                    found === nothing || break
                end
                found === nothing && return NotElementary(
                    "∫ (…)·$θterm: the order-$q part of the divisor of the residues is not torsion (T·Δ would " *
                    "have order $ord, but no N | $ord makes N·T_G·Δ principal)")
                found === :notrational && return ni("the logarithmic part found is not rational")
            end
        end
    end
    found === nothing && return ni("no torsion multiple N ≤ $Nmax of the divisor of the residues found")
    N, cs, Wsub = found
    ωt = [kum_ω_term(b0, C, j) for j in 0:(q - 1)]
    if degree(Mz) == q && q > 1 && σ != 1
        # z ↦ ζᶜz permutes the chosen places like τ: the log part is (b₀/N) Σ_{z^q = σ} z log v(z, x)
        zc = Any[nothing for _ in 1:q]
        for i in 0:(q - 1)
            tsi = Any[]
            for k in 0:(q - 1)
                pk = QX(Q[(i + 1 <= length(a.c.c) ? a.c.c[i + 1] : Q(0)) for a in cs[k + 1].c])
                iszero(pk) && continue
                t = poly_term(b0, pk)
                push!(tsi, k == 0 ? t : mk(b0, :*, t, ωt[k + 1]))
            end
            isempty(tsi) || (zc[i + 1] = length(tsi) == 1 ? tsi[1] : mk(b0, :+, tsi...))
        end
        return Wsub, ScaledRootSum(cterm(b0, bb / N), TermRootSum(Mz, zc, xk))
    end
    # output: (b₀σ^(1/q)/N) Σ_{α^q=1} α log(Σ_j cⱼ ωⱼ α^(-j))
    zt = σ == 1 ? b0.lift(1) : mk(b0, :^, b0.lift(σ), b0.lift(Q(1, q)))
    coeffs = Any[nothing for _ in 1:q]
    for k in 0:(q - 1)
        ck = kum_poly_term(b0, cs[k + 1], zt, σ, q)
        ck === nothing && continue
        coeffs[mod(-k, q) + 1] = k == 0 ? ck : mk(b0, :*, ck, ωt[k + 1])
    end
    fac = mk(b0, :*, cterm(b0, bb / N), zt)
    Wsub, ScaledRootSum(fac, TermRootSum(QX(vcat(Q[-1], zeros(Q, q - 1), Q[1])), coeffs, xk))
end

# ωⱼ as a term
function kum_ω_term(b0::Builder, C::KumCurve, j::Int)
    fs = Any[mk(b0, :^, poly_term(b0, C.bs[k]), b0.lift(C.fr[j + 1][k])) for k in eachindex(C.bs) if !iszero(C.fr[j + 1][k])]
    isempty(fs) ? b0.lift(1) : length(fs) == 1 ? fs[1] : mk(b0, :*, fs...)
end
# ωⱼ′/ωⱼ = Σₖ {j rₖ} bₖ′/bₖ over K
function kum_dlogω(::Type{K}, emb, C::KumCurve, j::Int) where {K}
    PL = UPoly{K}
    lift(f::QX) = PL(K[emb(c) for c in f.c])
    sum((frac(PL([emb(C.fr[j + 1][k])])) * frac(lift(deriv(C.bs[k])), lift(C.bs[k])) for k in eachindex(C.bs)
         if !iszero(C.fr[j + 1][k])); init = zero(Frac{PL}))
end
# ωᵢωⱼ = carry · ω_t, t = i + j mod q, carry = Π bₖ^(⌊t rₖ⌋ + ⌊(i+j)/q⌋ eₖ - ⌊i rₖ⌋ - ⌊j rₖ⌋)
function kum_carry(::Type{K}, emb, C::KumCurve, i::Int, j::Int) where {K}
    PL = UPoly{K}
    t, d = mod(i + j, C.q), (i + j) ÷ C.q
    cr = prod((C.bs[k]^(C.fl[t + 1][k] + d * C.es[k] - C.fl[i + 1][k] - C.fl[j + 1][k]) for k in eachindex(C.bs));
              init = one(QX))
    t, PL(K[emb(c) for c in cr.c])
end

struct KumBadPrime <: Exception end

# branch-0 data over K (L, or 𝔽_p with emb = reduction): (B, [gⱼ]) lifted, the places (F, n_F, S_F) with
# θ ≡ S_F, and the leading coefficient w of θ at the branch 0 of ∞
function kum_lp_data(::Type{K}, emb, z, C::KumCurve, fin, ts, ns, s∞, κ) where {K}
    PL = UPoly{K}
    lift(f::QX) = PL(K[emb(c) for c in f.c])
    gs = [prod((C.bs[k]^C.fl[j + 1][k] for k in eachindex(C.bs)); init = one(QX)) for j in 0:(C.q - 1)]
    cd = (B = lift(C.B), g = [lift(gj) for gj in gs])
    Sd = Tuple{PL,Int,PL}[]                             # (F, n_F, S_F)
    for (i, (F, s, hF)) in enumerate(fin)
        FL = lift(F)
        rF = z * emb(ts[i])                             # the residue t σ^(1/q) (z = σ^(1/q)) = h θ
        S = rem(PL([rF]) * hyp_invmod(lift(hF), FL), FL)
        push!(Sd, (FL, ns[i], S))
    end
    w = nothing
    s∞ === nothing || (w = -(z * emb(ts[end])) * emb(kum_lcprod(C, ones(Int, length(C.bs)))) / emb(κ))
    cd, Sd, w
end

# good reduction mod the current prime: the bases squarefree, of the same degrees, pairwise coprime, and the
# poles squarefree and coprime to them
function kum_good_mod(C::KumCurve, fin)
    bps = UPoly{ModP}[]
    for b in C.bs
        bp = hyp_map(modp, b, ModP)
        (bp === nothing || degree(bp) != degree(b) || degree(gcd(bp, deriv(bp))) != 0) && return false
        any(c -> degree(gcd(c, bp)) != 0, bps) && return false
        push!(bps, bp)
    end
    Ap = prod(bps; init = one(UPoly{ModP}))
    for (F, _, _) in fin
        Fp = hyp_map(modp, F, ModP)
        (Fp === nothing || degree(Fp) != degree(F) || degree(gcd(Fp, deriv(Fp))) != 0 ||
         degree(gcd(Fp, Ap)) != 0) && return false
    end
    true
end

# The order of Δ by reduction mod primes p ≥ 7 of good reduction (p ∤ q σ, `kum_good_mod`) with a root of
# the minimal polynomial Mz of σ^(1/q) mod p (a prime of degree 1 of L; unramified, so reduction is
# injective on torsion): :infinite (proved), N₁ (the order mod one prime, confirmed at two more), or nothing.
function kum_lp_order(C::KumCurve, fin, ts, ns, s∞, κ, n∞::Int, σ::Int, Mz::QX;
                      cap::Int = 40, pmax::Int = 400, nconfirm::Int = 2)
    q = C.q
    c1 = [k == 0 ? 1 : 0 for k in 0:(q - 1)]
    N1, conf = nothing, 0
    pr = 5
    while pr < pmax
        pr += 2
        is_probable_prime(big(pr)) || continue
        (pr % q == 0 || σ % pr == 0) && continue
        r = with_mod(pr) do
            emb = c -> (v = modp(c); v === nothing ? throw(KumBadPrime()) : v)
            try
                kum_good_mod(C, fin) || return nothing
                Mp = hyp_map(modp, Mz, ModP)
                Mp === nothing && return nothing
                rts = modp_roots(Mp)
                isempty(rts) && return nothing
                cd, Sd, w = kum_lp_data(ModP, emb, rts[1], C, fin, ts, ns, s∞, κ)
                (w !== nothing && iszero(w)) && return nothing
                principal(N) = (sys = kum_orbit_system(ModP, emb, cd, Sd, w, C, n∞, N, c1; maxu = 3000);
                                sys isa Tuple ? !isempty(nullspace_cols(sys[2], length(sys[2]))) : sys)
                if N1 === nothing
                    for N in 1:cap
                        t = principal(N)
                        t === :toolarge && return nothing
                        t === true && return (:order, N)
                    end
                    return nothing                      # order > cap here: try another prime
                end
                t = principal(N1)
                t === :toolarge && return nothing
                t === true ? :same : :different
            catch e
                (e isa KumBadPrime || e isa RischError || e isa DivideError) || rethrow()
                nothing
            end
        end
        r === nothing && continue
        r === :different && return :infinite
        if r isa Tuple
            N1 = r[2]
        else
            conf += 1
            conf >= nconfirm && return N1
        end
    end
    nothing
end

# ℚ(σ^(1/q)) ∩ ℚ(ζ_q) = ℚ (sufficient): for odd q always (L has a real embedding, odd-order abelian
# subfields of a pure field are trivial); for even q, σ > 0 and the only possible abelian subfield ℚ(√σ)
# (after taking σ = s² to s^(1/(q/2))) not inside ℚ(ζ_q): its conductor (|d| or 4|d|) does not divide q.
function kum_cyclo_disjoint(σ::Int, q::Int, q0::Int = q)
    isodd(q) && return true
    σ <= 0 && return false
    s = isqrt(σ)
    s * s == σ && return s == 1 || kum_cyclo_disjoint(s, q ÷ 2, q0)
    _, d = sqfree_split(big(σ))
    f = mod(d, 4) == 1 ? abs(d) : 4 * abs(d)
    q0 % f != 0
end

# T = Π_{ℓ | q prime} (1 - τ^(q/ℓ)) in ℤ[τ]/(τ^q - 1): its coefficients c₀ … c_{q-1}
function kum_T(q::Int)
    c = zeros(Int, q)
    c[1] = 1
    for (ℓ, _) in factorint(big(q))
        k = q ÷ Int(ℓ)
        c2 = copy(c)
        for i in 0:(q - 1)
            c2[mod(i + k, q) + 1] -= c[i + 1]
        end
        c = c2
    end
    c
end

# the multiplicities of N·c·Δ at the places τᵏP_F, shifted by full fibers to be ≥ 0, the pole orders at the
# branches of ∞ (q | m, n∞ ≠ 0; else nothing) and the degree bounds of the cⱼ; nothing when N·c·Δ is not
# integral
function kum_shape(C::KumCurve, Sd, n∞::Int, N::Int, c::Vector{Int})
    q = C.q
    mults = Vector{Int}[]
    for (_, n, _) in Sd
        mk = [N * n * c[k + 1] for k in 0:(q - 1)]
        push!(mults, mk .- minimum(mk))
    end
    Z = sum((sum(mults[i]) * degree(Sd[i][1]) for i in eachindex(Sd)); init = 0)
    if n∞ == 0
        # the q/den(ρ) places at ∞, each of ramification den(ρ): balanced pole orders, i.e.
        # q (deg cⱼ + ρⱼ) ≤ Z (no cancellation between the j)
        Z % (q ÷ Int(denominator(C.ρ))) == 0 || return nothing
        return mults, nothing, [floor(Int, Q(Z, q) - C.ρs[j + 1]) for j in 0:(q - 1)]
    end
    a = [N * n∞ * c[j + 1] for j in 0:(q - 1)]
    a = a .- minimum(a)
    (Z + sum(a)) % q == 0 || return nothing
    O = (Z + sum(a)) ÷ q
    os = [O - a[j + 1] for j in 0:(q - 1)]
    omax = maximum(os)
    omax < 0 && return nothing
    mults, os, [floor(Int, Q(omax) - C.ρs[j + 1]) for j in 0:(q - 1)]
end

# for each j: (the leading coefficient wʲ/Π lcₖ^⌊j rₖ⌋, the series Sⱼ(1/x)) of ωⱼ = lead · x^ρⱼ Sⱼ(1/x) at
# the branch 0 of ∞
function kum_inf_coeffs(::Type{K}, emb, C::KumCurve, w, len::Int) where {K}
    [(w^j * emb(inv(kum_lcprod(C, C.fl[j + 1]))), K[emb(cc) for cc in kum_series(C, C.fr[j + 1], len)])
     for j in 0:(C.q - 1)]
end

# the system for N·c·Δ over a field K ∋ ζ (ζ of order q): per-branch multiplicities at the places
# τᵏP_F (θ ≡ ζᵏ S_F) and per-branch pole orders at ∞; v = Σ cⱼ ωⱼ, ωⱼ = θʲ/gⱼ
function kum_branch_system(::Type{K}, emb, cd, Sd, w, C::KumCurve, n∞::Int, N::Int, c::Vector{Int}, ζ;
                           maxu::Int = 3000) where {K}
    q = C.q
    PL = UPoly{K}
    sh = kum_shape(C, Sd, n∞, N, c)
    sh === nothing && return nothing
    mults, os, dks = sh
    unknowns = [(k, j) for k in 0:(q - 1) for j in 0:dks[k + 1]]
    isempty(unknowns) && return nothing
    length(unknowns) > maxu && return :toolarge
    x = xpoly(K)
    conds = []                                          # (G^e, [ωⱼ at the branch mod G^e])
    for (i, (F, _, S)) in enumerate(Sd)
        emax = maximum(mults[i])
        emax == 0 && continue
        Θ = kum_root_lift(cd.B, S, F, emax, q)
        for k in 0:(q - 1)
            e = mults[i][k + 1]
            e == 0 && continue
            Ge = F^e
            Θk = PL([ζ^k]) * Θ
            push!(conds, (Ge, [rem(Θk^j * hyp_invmod(rem(cd.g[j + 1], Ge), Ge), Ge) for j in 0:(q - 1)]))
        end
    end
    ic = os === nothing ? nothing : kum_inf_coeffs(K, emb, C, w, maximum(os) + maximum(dks) + 2)
    cols = Vector{K}[]
    for (k, j) in unknowns
        col = K[]
        for (Ge, ωv) in conds
            rr = rem(x^j * ωv[k + 1], Ge)
            append!(col, [d <= length(rr.c) ? rr.c[d] : zero(K) for d in 1:degree(Ge)])
        end
        if os !== nothing                               # branch jb: Σ_k ζ^(jb k) E_k(t) = 0 for t > o_jb
            lw, sk = ic[k + 1]
            s0 = j + Int(C.ρs[k + 1])
            E(t) = (0 <= s0 - t <= length(sk) - 1) ? lw * sk[s0 - t + 1] : zero(K)
            for jb in 0:(q - 1), t in (os[jb + 1] + 1):maximum(os)
                push!(col, ζ^(jb * k) * E(t))
            end
        end
        push!(cols, col)
    end
    unknowns, cols
end

# as kum_lp_order, for N·T·Δ, at primes p ≡ 1 mod q (ζ_q ∈ 𝔽_p): :infinite (proved), N₁, or nothing
function kum_lp_order_T(C::KumCurve, fin, ts, ns, s∞, κ, n∞::Int, σ::Int, Mz::QX;
                        c::Vector{Int} = kum_T(C.q), cap::Int = 40, pmax::Int = 1200, nconfirm::Int = 2)
    q = C.q
    ℓs = [Int(ℓ) for (ℓ, _) in factorint(big(q))]
    N1, conf = nothing, 0
    pr = 1
    while pr < pmax
        pr += q
        (pr >= 7 && is_probable_prime(big(pr)) && σ % pr != 0) || continue
        r = with_mod(pr) do
            emb = c0 -> (v = modp(c0); v === nothing ? throw(KumBadPrime()) : v)
            try
                kum_good_mod(C, fin) || return nothing
                Mp = hyp_map(modp, Mz, ModP)
                Mp === nothing && return nothing
                rts = modp_roots(Mp)
                isempty(rts) && return nothing
                ζ = nothing                             # an element of order exactly q
                for g in 2:(pr - 1)
                    z0 = ModP(powermod(g, (pr - 1) ÷ q, pr))
                    all(ℓ -> !isone(z0^(q ÷ ℓ)), ℓs) && (ζ = z0; break)
                end
                ζ === nothing && return nothing
                cd, Sd, w = kum_lp_data(ModP, emb, rts[1], C, fin, ts, ns, s∞, κ)
                (w !== nothing && iszero(w)) && return nothing
                principal(N) = (sys = kum_branch_system(ModP, emb, cd, Sd, w, C, n∞, N, c, ζ);
                                sys isa Tuple ? !isempty(nullspace_cols(sys[2], length(sys[2]))) : sys)
                if N1 === nothing
                    for N in 1:cap
                        t = principal(N)
                        t === :toolarge && return nothing
                        t === true && return (:order, N)
                    end
                    return nothing
                end
                t = principal(N1)
                t === :toolarge && return nothing
                t === true ? :same : :different
            catch e
                (e isa KumBadPrime || e isa RischError || e isa DivideError) || rethrow()
                nothing
            end
        end
        r === nothing && continue
        r === :different && return :infinite
        if r isa Tuple
            N1 = r[2]
        else
            conf += 1
            conf >= nconfirm && return N1
        end
    end
    nothing
end

# T_G = Σ_{a ∈ (ℤ/q)*} T(τ^a): coefficients, invariant under k ↦ a k
function kum_TG(q::Int)
    c = kum_T(q)
    cG = zeros(Int, q)
    for a in 1:(q - 1)
        gcd(a, q) == 1 || continue
        for k in 0:(q - 1)
            cG[mod(a * k, q) + 1] += c[k + 1]
        end
    end
    cG
end

function kum_moebius(n::Int)
    r = 1
    for (_, e) in factorint(big(n))
        e > 1 && return 0
        r = -r
    end
    r
end
kum_totient(n::Int) = prod((Int(ℓ)^(e - 1) * (Int(ℓ) - 1) for (ℓ, e) in factorint(big(n))); init = 1)
# Ramanujan's sum c_d(m) = Σ_{ζ of order d} ζ^m
kum_ramanujan(d::Int, m::Int) = (g = gcd(d, mod(m, d) == 0 ? d : m);
                                  kum_moebius(d ÷ g) * kum_totient(d) ÷ kum_totient(d ÷ g))
# Θ = χ(T_G) for χ(τ) = ζ^p (gcd(p, q) = 1): Σ_k c_k ζ^(kp) = Σ over orbits c_O μ(q/gcd(k, q))
kum_Theta(cG::Vector{Int}, q::Int) = sum(cG[k + 1] * kum_ramanujan(q ÷ gcd(k, q), 1) // kum_totient(q ÷ gcd(k, q))
                                         for k in 0:(q - 1)) |> x -> (isone(denominator(x)) ? Int(x) : x)

# the branches 0 … q-1 grouped into Galois orbits (by the order d = q/gcd(k, q) of ζᵏ)
kum_orbit(q::Int, k::Int) = q ÷ gcd(k, q)

# The system for N·c·Δ over L (no ζ; c = 1 for Δ itself, c = T_G): multiplicities m_k = N n c_k at the
# places τᵏP_F (θ ≡ ζᵏS), shifted by full fibers to be ≥ 0; each level set J = {k : m_k ≥ e} is a union of
# orbits, and "v vanishes to order e on J" is v ≡ 0 mod (F^e, Q_J(θ)), Q_J = Π_{orbits d ⊆ J} Θ^φ(d) Φ_d(θ/Θ),
# with v = Σ cⱼ gⱼ⁻¹ θʲ near F. At ∞ (q | m, n∞ ≠ 0) the zero orders a_j = N n∞ c_j (shifted) and the pole
# orders o_j: for each t the set {j : o_j < t} is a union of orbits, and "Σ_k ζ^(jk) E_k(t) = 0 for j in an
# orbit d" is Σ_k c_d(k - k₀) E_k(t) = 0 for all k₀ (Ramanujan sums: rational).
function kum_orbit_system(::Type{K}, emb, cd, Sd, w, C::KumCurve, n∞::Int, N::Int, c::Vector{Int};
                          maxu::Int = 3000) where {K}
    q = C.q
    PL = UPoly{K}
    divs = [d for d in 1:q if q % d == 0]
    cyc = Dict(d => kum_cyclotomic(d) for d in divs)
    sh = kum_shape(C, Sd, n∞, N, c)
    sh === nothing && return nothing
    mults, os, dks = sh
    unknowns = [(k, j) for k in 0:(q - 1) for j in 0:dks[k + 1]]
    isempty(unknowns) && return nothing
    length(unknowns) > maxu && return :toolarge
    x = xpoly(K)
    conds = []                                          # (F^e, [gⱼ⁻¹ θʲ mod (F^e, Q_J) as coefficient lists])
    for (i, (F, _, S)) in enumerate(Sd)
        levels = sort!(unique(filter(>(0), mults[i])))
        isempty(levels) && continue
        Θ = kum_root_lift(cd.B, S, F, maximum(levels), q)
        for e in levels
            Ge = F^e
            Θe = rem(Θ, Ge)
            J = [k for k in 0:(q - 1) if mults[i][k + 1] >= e]
            QJ = [one(PL)]                              # coefficients in θ, low → high
            for d in divs
                ks = [k for k in 0:(q - 1) if kum_orbit(q, k) == d]
                all(k -> k in J, ks) || continue
                Φ = cyc[d]
                fac = [rem(PL([emb(Φ.c[i2 + 1])]) * Θe^(degree(Φ) - i2), Ge) for i2 in 0:degree(Φ)]
                QJ = kum_ypoly_mul(QJ, fac, Ge)
            end
            nJ = length(QJ) - 1
            nJ == 0 && continue
            red = Vector{PL}[]                          # θʲ mod Q_J (monic in θ), times gⱼ⁻¹
            cur = [i2 == 1 ? one(PL) : zero(PL) for i2 in 1:nJ]
            for jj in 0:(q - 1)
                gi = hyp_invmod(rem(cd.g[jj + 1], Ge), Ge)
                push!(red, [rem(ci * gi, Ge) for ci in cur])
                top = cur[nJ]
                cur = [i2 == 1 ? zero(PL) : cur[i2 - 1] for i2 in 1:nJ]
                for i2 in 1:nJ
                    cur[i2] = rem(cur[i2] - top * QJ[i2], Ge)
                end
            end
            push!(conds, (Ge, red))
        end
    end
    ic = os === nothing ? nothing : kum_inf_coeffs(K, emb, C, w, maximum(os) + maximum(dks) + 2)
    cols = Vector{K}[]
    for (k, j) in unknowns
        col = K[]
        for (Ge, red) in conds
            for ci in red[k + 1]
                rr = rem(x^j * ci, Ge)
                append!(col, [d <= length(rr.c) ? rr.c[d] : zero(K) for d in 1:degree(Ge)])
            end
        end
        if os !== nothing
            lw, sk = ic[k + 1]
            s0 = j + Int(C.ρs[k + 1])
            E(t) = (0 <= s0 - t <= length(sk) - 1) ? lw * sk[s0 - t + 1] : zero(K)
            for t in (minimum(os) + 1):maximum(os)
                Jt = [jb for jb in 0:(q - 1) if os[jb + 1] < t]
                for d in divs
                    js = [jb for jb in 0:(q - 1) if kum_orbit(q, jb) == d]
                    all(jb -> jb in Jt, js) || continue
                    for k0 in 0:(q - 1)
                        push!(col, emb(Q(kum_ramanujan(d, k - k0))) * E(t))
                    end
                end
            end
        end
        push!(cols, col)
    end
    unknowns, cols
end

# the cyclotomic polynomial Φ_d over ℚ
function kum_cyclotomic(d::Int)
    f = QX(vcat(Q[-1], zeros(Q, d - 1), Q[1]))          # x^d - 1
    for e in 1:(d - 1)
        d % e == 0 && (f = quo(f, kum_cyclotomic(e)))
    end
    f
end

# product of two polynomials in y with coefficients in L[x] mod G
function kum_ypoly_mul(a::Vector{P}, b::Vector{P}, G::P) where {P<:UPoly}
    r = [zero(P) for _ in 1:(length(a) + length(b) - 1)]
    for i in eachindex(a), j in eachindex(b)
        r[i + j - 1] = rem(r[i + j - 1] + a[i] * b[j], G)
    end
    r
end

# an element of L(x) with rational coefficients, in ℚ(x) (or nothing)
kum_down(f::QXF) = f
function kum_down(f::Frac{UPoly{NFz}})
    dn(p) = all(c -> degree(c.c) <= 0, p.c) ? QX(Q[isempty(c.c.c) ? Q(0) : c.c.c[1] for c in p.c]) : nothing
    n, d = dn(f.num), dn(f.den)
    (n === nothing || d === nothing) ? nothing : frac(n, d)
end

# a polynomial in x over ℚ or L = ℚ(σ^(1/q)) as a term (σ^(1/q) as zt)
kum_poly_term(b0::Builder, c::QX, zt, σ, q) = iszero(c) ? nothing : poly_term(b0, c)
function kum_poly_term(b0::Builder, c::UPoly{NFz}, zt, σ, q)
    iszero(c) && return nothing
    ts = Any[]
    for i in 0:(q - 1)                                  # Σ_i (Σ_d a_{d,i} x^d) zt^i
        pi = QX(Q[(i + 1 <= length(a.c.c) ? a.c.c[i + 1] : Q(0)) for a in c.c])
        iszero(pi) && continue
        t = poly_term(b0, pi)
        push!(ts, i == 0 ? t : mk(b0, :*, t, i == 1 ? zt : mk(b0, :^, zt, b0.lift(i))))
    end
    isempty(ts) ? nothing : length(ts) == 1 ? ts[1] : mk(b0, :+, ts...)
end
