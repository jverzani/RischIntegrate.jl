# ---------------------------------------------------------------------------
# SI2 phase 3b: the log part for one radical, θ = yᵖ, y = b^(1/q) (b squarefree, gcd(p, q) = 1)
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

# the log part (Wsub, ScaledRootSum) with d/dx(log part) = Wsub θ, or the exception to raise
function kum_log_part(b::QX, p::Int, q::Int, P::QX, R::QX, D::QX, θterm, b0::Builder, xk::String; Nmax::Int = 8)
    m = degree(b)
    ni(msg) = RischNotImplemented("∫ (…)·$θterm: $msg (SI2 phase 3b)")
    pinv = invmod(p, q)
    dD = deriv(D)
    # residue data: (F, s) at finite places; s∞ (with κ) at ∞
    fin = Tuple{QX,Q,QX}[]                              # (F, s, h mod F)
    if !iszero(R)
        for F in factor_Q(D)
            hF = rem(R * hyp_invmod(b * dD, F), F)
            sF = rem(hF^q * b^p, F)
            degree(sF) == 0 || return ni("residues of degree > q over ℚ")
            push!(fin, (F, sF.c[1], hF))
        end
    end
    κ = Q(0)
    if isone(denominator(Q(p * m, q))) && !iszero(P)
        N0 = degree(P) + 2
        sr = hyp_sqrt_series(b, N0, Q(p, q) - 1)
        e0 = (p * m) ÷ q - m
        κ = sum((P.c[j + 1] * sr[j + e0 + 2] for j in 0:degree(P) if 0 <= j + e0 + 1 <= N0); init = Q(0))
    end
    s∞ = iszero(κ) ? nothing : (-κ)^q * lc(b)^(p - q)   # r∞ = -w^(p-q) κ, w^q = lc(b)
    cls = [kum_qclass(s, q) for (_, s, _) in fin]
    s∞ === nothing || push!(cls, kum_qclass(s∞, q))
    isempty(cls) && return ni("no residues found")
    σ = cls[1][2]
    all(c -> c[2] == σ, cls) || return ni("residues in several classes")
    ts = [c[1] for c in cls]
    (all(t -> t > 0, ts) || all(t -> t < 0, ts)) || return ni("residues of both signs")
    bb = reduce(gcd, abs.(ts)) * sign(ts[1])
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
    search(Ns, maxu) = run() do K, emb, z
        PL = UPoly{K}
        bL, Sd, w = kum_lp_data(K, emb, z, b, p, q, fin, ts, ns, s∞, κ)
        for N in Ns
            sys = kum_lp_system(K, emb, bL, Sd, w, b, q, n∞, N; maxu = maxu)
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
            # η = v′/v in L(x)[y]/(y^q - b): v′ = Σ (c_k′ + k c_k b′/(q b)) y^k
            F_ = Frac{PL}
            fb = frac(bL)
            dv = F_[frac(deriv(cs[k + 1])) + frac(cs[k + 1]) * frac(PL([emb(Q(k, q))])) * frac(deriv(bL)) / fb for k in 0:(q - 1)]
            mcols = Vector{F_}[]
            for jj in 0:(q - 1)                         # v·y^jj
                col = [zero(F_) for _ in 1:q]
                for k in 0:(q - 1)
                    d, rmd = divrem(k + jj, q)
                    col[rmd + 1] = col[rmd + 1] + frac(cs[k + 1]) * fb^d
                end
                push!(mcols, col)
            end
            η = solve_columns(mcols, dv)
            η === nothing && throw(RischError("kum_log_part: v is not invertible"))
            λ = z * emb(Q(q) * bb / N)
            Wl = η[p + 1] * frac(PL([λ]))
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
        ord = kum_lp_order(b, p, q, fin, ts, ns, s∞, κ, n∞, σ, Mz)
        ord === :infinite && return NotElementary(
            "∫ (…)·$θterm: the divisor of the residues has infinite order in the Jacobian of y^$q = b " *
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
        # kills the others and not these, which are conjugate (L ∩ ℚ(ζ_q) = ℚ): elementary iff T·[Δ] is
        # torsion. T·Δ needs ζ_q: its orders are computed mod primes p ≡ 1 mod q only.
        ord = kum_lp_order_T(b, p, q, fin, ts, ns, s∞, κ, n∞, σ, Mz)
        ord === :infinite && return NotElementary(
            "∫ (…)·$θterm: the order-$q part of the divisor of the residues has infinite order in the " *
            "Jacobian of y^$q = b (its orders modulo two primes differ)")
        ord isa Int && return ni("the order-$q part of the divisor of the residues is probably torsion (order " *
                                 "$ord mod p); the logarithmic part over ℚ(σ^(1/q), ζ_q) is not implemented")
    end
    found === nothing && return ni("no torsion multiple N ≤ $Nmax of the divisor of the residues found")
    N, cs, Wsub = found
    yt = mk(b0, :^, poly_term(b0, b), b0.lift(Q(1, q)))
    if degree(Mz) == q && q > 1 && σ != 1
        # z ↦ ζᶜz permutes the chosen places like τ: the log part is (b₀/N) Σ_{z^q = σ} z log v(z, x, y)
        zc = Any[nothing for _ in 1:q]
        for i in 0:(q - 1)
            ts = Any[]
            for k in 0:(q - 1)
                pk = QX(Q[(i + 1 <= length(a.c.c) ? a.c.c[i + 1] : Q(0)) for a in cs[k + 1].c])
                iszero(pk) && continue
                t = poly_term(b0, pk)
                push!(ts, k == 0 ? t : mk(b0, :*, t, k == 1 ? yt : mk(b0, :^, yt, b0.lift(k))))
            end
            isempty(ts) || (zc[i + 1] = length(ts) == 1 ? ts[1] : mk(b0, :+, ts...))
        end
        return Wsub, ScaledRootSum(cterm(b0, bb / N), TermRootSum(Mz, zc, xk))
    end
    # output: (b₀σ^(1/q)/N) Σ_{α^q=1} α log(Σ_k c_k yᵏ α^(e_k)), e_k = -p′k mod q
    zt = σ == 1 ? b0.lift(1) : mk(b0, :^, b0.lift(σ), b0.lift(Q(1, q)))
    coeffs = Any[nothing for _ in 1:q]
    for k in 0:(q - 1)
        ck = kum_poly_term(b0, cs[k + 1], zt, σ, q)
        ck === nothing && continue
        t = k == 0 ? ck : mk(b0, :*, ck, k == 1 ? yt : mk(b0, :^, yt, b0.lift(k)))
        coeffs[mod(-pinv * k, q) + 1] = t
    end
    fac = mk(b0, :*, cterm(b0, bb / N), zt)
    Wsub, ScaledRootSum(fac, TermRootSum(QX(vcat(Q[-1], zeros(Q, q - 1), Q[1])), coeffs, xk))
end

struct KumBadPrime <: Exception end

# branch-0 data over K (L, or 𝔽_p with emb = reduction): b, the places (F, n_F, S_F) and w at ∞
function kum_lp_data(::Type{K}, emb, z, b::QX, p::Int, q::Int, fin, ts, ns, s∞, κ) where {K}
    PL = UPoly{K}
    pinv = invmod(p, q)
    lift(f::QX) = PL(K[emb(c) for c in f.c])
    bL = lift(b)
    Sd = Tuple{PL,Int,PL}[]                             # (F, n_F, S_F)
    for (i, (F, s, hF)) in enumerate(fin)
        FL = lift(F)
        rF = z * emb(ts[i])                             # the residue t σ^(1/q) (z = σ^(1/q))
        yp = rem(PL([rF]) * hyp_invmod(lift(hF), FL), FL)
        S = rem(yp^pinv * hyp_invmod(bL^((p * pinv - 1) ÷ q), FL), FL)
        push!(Sd, (FL, ns[i], S))
    end
    w = nothing
    if s∞ !== nothing                                   # w^(p-q) = -r∞/κ, w^p = w^(p-q) lc, w = (w^p)^p′/lc^((pp′-1)/q)
        wpq = -(z * emb(ts[end])) / emb(κ)
        w = (wpq * emb(lc(b)))^pinv / emb(lc(b))^((p * pinv - 1) ÷ q)
    end
    bL, Sd, w
end

# the linear system for v with div(v) = N·Δ (see kum_log_part): (unknowns, columns), nothing when N·Δ is
# not integral, :toolarge
function kum_lp_system(::Type{K}, emb, bL, Sd, w, b::QX, q::Int, n∞::Int, N::Int; maxu::Int = 800) where {K}
    m = degree(b)
    es = [N * n for (_, n, _) in Sd]
    Z = sum((es[i] * degree(Sd[i][1]) for i in eachindex(Sd)); init = 0)
    if n∞ == 0
        # gcd(m, q) places at ∞, each of ramification q/gcd: balanced pole orders Z/gcd each, i.e.
        # q deg c_k + k m ≤ Z (no cancellation between the k: different orders mod q/gcd)
        Z % gcd(m, q) == 0 || return nothing
        o0 = o1 = omax = 0
        dks = [fld(Z - k * m, q) for k in 0:(q - 1)]
    else                                                # q | m: q unramified places at ∞
        (Z + N * n∞) % q == 0 || return nothing
        o1 = (Z + N * n∞) ÷ q
        o0 = o1 - N * n∞
        omax = max(o0, o1)
        omax < 0 && return nothing
        dks = [floor(Int, Q(omax) - Q(k * m, q)) for k in 0:(q - 1)]
    end
    unknowns = [(k, j) for k in 0:(q - 1) for j in 0:dks[k + 1]]
    isempty(unknowns) && return nothing
    length(unknowns) > maxu && return :toolarge
    mods = [(F^es[i], kum_root_lift(bL, S, F, es[i], q)) for (i, (F, _, S)) in enumerate(Sd)]
    ypows = [[rem(Y^k, Ge) for k in 0:(q - 1)] for (Ge, Y) in mods]
    ser = n∞ == 0 ? nothing : [K[emb(c) for c in hyp_sqrt_series(b, omax + m + 2, Q(k, q))] for k in 0:(q - 1)]
    x = xpoly(K)
    cols = Vector{K}[]
    for (k, j) in unknowns
        col = K[]
        for (i, (Ge, _)) in enumerate(mods)
            rr = rem(x^j * ypows[i][k + 1], Ge)
            append!(col, [d <= length(rr.c) ? rr.c[d] : zero(K) for d in 1:degree(Ge)])
        end
        if n∞ != 0                                      # E_k(t) = w^k [T^k]_(j + km/q - t)
            sh = j + (k * m) ÷ q
            E(t) = (0 <= sh - t <= length(ser[k + 1]) - 1) ? w^k * ser[k + 1][sh - t + 1] : zero(K)
            if o0 < o1                                  # branch 0: Σ_k E_k(t) = 0 for o0 < t ≤ o1
                for t in (o0 + 1):o1
                    push!(col, E(t))
                end
            else                                        # other branches: E_k(t) = E_0(t) for o1 < t ≤ o0
                for t in (o1 + 1):o0, k2 in 1:(q - 1)
                    push!(col, k == k2 ? E(t) : k == 0 ? -E(t) : zero(K))
                end
            end
        end
        push!(cols, col)
    end
    unknowns, cols
end

# The order of Δ by reduction mod primes p ≥ 7 of good reduction (p ∤ q σ lc(b) disc(b), b and the poles
# squarefree and coprime mod p) with a root of the minimal polynomial Mz of σ^(1/q) mod p (a prime of
# degree 1 of L; unramified, so reduction is injective on torsion): :infinite (proved), N₁ (the order mod
# one prime, confirmed at two more), or nothing.
function kum_lp_order(b::QX, p::Int, q::Int, fin, ts, ns, s∞, κ, n∞::Int, σ::Int, Mz::QX;
                      cap::Int = 40, pmax::Int = 400, nconfirm::Int = 2)
    N1, conf = nothing, 0
    pr = 5
    while pr < pmax
        pr += 2
        is_probable_prime(big(pr)) || continue
        (pr % q == 0 || σ % pr == 0) && continue
        r = with_mod(pr) do
            emb = c -> (v = modp(c); v === nothing ? throw(KumBadPrime()) : v)
            try
                bp = hyp_map(modp, b, ModP)
                (bp === nothing || degree(bp) != degree(b) || degree(gcd(bp, deriv(bp))) != 0) && return nothing
                for (F, _, _) in fin
                    Fp = hyp_map(modp, F, ModP)
                    (Fp === nothing || degree(Fp) != degree(F) || degree(gcd(Fp, deriv(Fp))) != 0 ||
                     degree(gcd(Fp, bp)) != 0) && return nothing
                end
                Mp = hyp_map(modp, Mz, ModP)
                Mp === nothing && return nothing
                rts = modp_roots(Mp)
                isempty(rts) && return nothing
                bL, Sd, w = kum_lp_data(ModP, emb, rts[1], b, p, q, fin, ts, ns, s∞, κ)
                (w !== nothing && iszero(w)) && return nothing
                principal(N) = (sys = kum_lp_system(ModP, emb, bL, Sd, w, b, q, n∞, N; maxu = 3000);
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

# the system for N·T·Δ over a field K ∋ ζ (ζ of order q): per-branch multiplicities at the places
# τᵏP_F (y ≡ ζᵏ S_F) and at the branches of ∞ (q | m), shifted by full fibers to be ≥ 0
function kum_branch_system(::Type{K}, emb, bL, Sd, w, b::QX, q::Int, n∞::Int, N::Int, c::Vector{Int}, ζ;
                           maxu::Int = 3000) where {K}
    m = degree(b)
    PL = UPoly{K}
    mults = Vector{Int}[]
    for (_, n, _) in Sd
        mk = [N * n * c[k + 1] for k in 0:(q - 1)]
        push!(mults, mk .- min(0, minimum(mk)))
    end
    Z = sum((sum(mults[i]) * degree(Sd[i][1]) for i in eachindex(Sd)); init = 0)
    if n∞ == 0
        Z % gcd(m, q) == 0 || return nothing
        dks = [fld(Z - k * m, q) for k in 0:(q - 1)]
        os = nothing
    else                                                # q | m: zero orders a_j at the branches of ∞
        a = [N * n∞ * c[j + 1] for j in 0:(q - 1)]
        (Z + sum(a)) % q == 0 || return nothing
        O = (Z + sum(a)) ÷ q
        os = [O - a[j + 1] for j in 0:(q - 1)]          # pole orders
        omax = maximum(os)
        omax < 0 && return nothing
        dks = [floor(Int, Q(omax) - Q(k * m, q)) for k in 0:(q - 1)]
    end
    unknowns = [(k, j) for k in 0:(q - 1) for j in 0:dks[k + 1]]
    isempty(unknowns) && return nothing
    length(unknowns) > maxu && return :toolarge
    x = xpoly(K)
    conds = []                                          # (G^e, ζᵏY powers)
    for (i, (F, _, S)) in enumerate(Sd)
        emax = maximum(mults[i])
        emax == 0 && continue
        Y = kum_root_lift(bL, S, F, emax, q)
        for k in 0:(q - 1)
            e = mults[i][k + 1]
            e == 0 && continue
            Ge = F^e
            Yk = PL([ζ^k]) * Y
            push!(conds, (Ge, [rem(Yk^i, Ge) for i in 0:(q - 1)]))
        end
    end
    ser = os === nothing ? nothing : [K[emb(cc) for cc in hyp_sqrt_series(b, maximum(os) + m + 2, Q(k, q))] for k in 0:(q - 1)]
    cols = Vector{K}[]
    for (k, j) in unknowns
        col = K[]
        for (Ge, yp) in conds
            rr = rem(x^j * yp[k + 1], Ge)
            append!(col, [d <= length(rr.c) ? rr.c[d] : zero(K) for d in 1:degree(Ge)])
        end
        if os !== nothing                               # branch jb: Σ_k ζ^(jb k) E_k(t) = 0 for t > o_jb
            sh = j + (k * m) ÷ q
            E(t) = (0 <= sh - t <= length(ser[k + 1]) - 1) ? w^k * ser[k + 1][sh - t + 1] : zero(K)
            for jb in 0:(q - 1), t in (os[jb + 1] + 1):maximum(os)
                push!(col, ζ^(jb * k) * E(t))
            end
        end
        push!(cols, col)
    end
    unknowns, cols
end

# as kum_lp_order, for N·T·Δ, at primes p ≡ 1 mod q (ζ_q ∈ 𝔽_p): :infinite (proved), N₁, or nothing
function kum_lp_order_T(b::QX, p::Int, q::Int, fin, ts, ns, s∞, κ, n∞::Int, σ::Int, Mz::QX;
                        cap::Int = 40, pmax::Int = 1200, nconfirm::Int = 2)
    c = kum_T(q)
    ℓs = [Int(ℓ) for (ℓ, _) in factorint(big(q))]
    N1, conf = nothing, 0
    pr = 1
    while pr < pmax
        pr += q
        (pr >= 7 && is_probable_prime(big(pr)) && σ % pr != 0) || continue
        r = with_mod(pr) do
            emb = c0 -> (v = modp(c0); v === nothing ? throw(KumBadPrime()) : v)
            try
                bp = hyp_map(modp, b, ModP)
                (bp === nothing || degree(bp) != degree(b) || degree(gcd(bp, deriv(bp))) != 0) && return nothing
                for (F, _, _) in fin
                    Fp = hyp_map(modp, F, ModP)
                    (Fp === nothing || degree(Fp) != degree(F) || degree(gcd(Fp, deriv(Fp))) != 0 ||
                     degree(gcd(Fp, bp)) != 0) && return nothing
                end
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
                bL, Sd, w = kum_lp_data(ModP, emb, rts[1], b, p, q, fin, ts, ns, s∞, κ)
                (w !== nothing && iszero(w)) && return nothing
                principal(N) = (sys = kum_branch_system(ModP, emb, bL, Sd, w, b, q, n∞, N, c, ζ);
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
