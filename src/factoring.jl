# ---------------------------------------------------------------------------
# Small helpers: integer factoring, rational roots, Gaussian rationals
# ---------------------------------------------------------------------------
function factorint(n::BigInt)
    f = Pair{BigInt,Int}[]
    p = big(2)
    while p * p <= n && p < 1_000_000
        k = 0
        while n % p == 0
            n ÷= p
            k += 1
        end
        k > 0 && push!(f, p => k)
        p += (p == 2 ? 1 : 2)
    end
    n > 1 && push!(f, n => 1)
    f
end

function divisors(n::BigInt)
    ds = BigInt[1]
    for (p, k) in factorint(n)
        ds = BigInt[d * p^e for d in ds for e in 0:k]
    end
    ds
end

# distinct rational roots of p, by the big prime method of factor_Q restricted to linear factors:
# the roots of p modulo a prime p₀ > 2·|lc F|·B (F the primitive integer form, B = 2ⁿ‖F‖₂ bounds the
# coefficients of any factor) are the roots of gcd(xᵖ⁰ - x, F) split by Cantor–Zassenhaus; a
# rational root a/b gives the factor (lc F/b)(b x - a) of lc F·F, whose constant term is the
# symmetric residue of -lc F·r. Every candidate is checked exactly. (The rational root theorem
# would need the divisors of the end coefficients, hopeless when they are large.)
function rational_roots(p::UPoly{Q})
    roots = Q[]
    iszero(p) && return roots
    c = copy(p.c)
    if iszero(c[1])
        push!(roots, Q(0))
        while !isempty(c) && iszero(c[1])
            popfirst!(c)
        end
    end
    length(c) <= 1 && return roots
    q = UPoly{Q}(c)
    degree(q) == 1 && return push!(roots, -c[1] / c[2])
    l = reduce(lcm, denominator.(c))
    F = BigInt[numerator(x * l) for x in c]
    F = F .÷ reduce(gcd, F)
    n = length(F) - 1
    p0 = 2 * abs(F[end]) * big(2)^n * (isqrt(sum(x^2 for x in F)) + 1) + 1
    while !is_probable_prime(p0)
        p0 += 1
    end
    fm = fp_monic(fp_norm(F, p0), p0)
    g = fp_gcd(fm, fp_sub(fp_powmod(BigInt[0, 1], p0, fm, p0), BigInt[0, 1], p0), p0)
    length(g) <= 1 && return roots
    for h in fp_edf(g, 1, p0, Ref(big(20240611)))
        s = mod(-F[end] * h[1], p0)
        s > p0 ÷ 2 && (s -= p0)
        r = Q(s) // Q(F[end])
        iszero(peval(q, r)) && push!(roots, r)
    end
    roots
end

# distinct roots in the constant field C of a polynomial over C. Contract: the result may be
# INCOMPLETE (a field may only find some of its roots, see ℚ(√d)); every caller divides out the
# roots found and treats a leftover factor of positive degree as "not handled"
# (RischNotImplemented / `unresolved`), never as "no roots". For ℚ the result is complete.
constant_roots(p::UPoly{Q}) = rational_roots(p)
constant_roots(p::UPoly) = throw(RischNotImplemented(
    "root finding in this constant field is not implemented"))

function rat_sqrt(a::Q)
    a < 0 && return nothing
    n, d = isqrt(numerator(a)), isqrt(denominator(a))
    (n^2 == numerator(a) && d^2 == denominator(a)) ? Q(n) // Q(d) : nothing
end

# the rational m-th root of a (m odd), or nothing
function rat_root(a::Q, m::Int)
    iroot(n::BigInt) = (r = round(BigInt, BigFloat(abs(n))^(1 / m)); for c in (r - 1, r, r + 1); c^m == abs(n) && return sign(n) * c; end; nothing)
    n, d = iroot(numerator(a)), iroot(denominator(a))
    (n === nothing || d === nothing) ? nothing : Q(n) // Q(d)
end

# step RP: a radicand u = c·w^m (m odd, c = r^m with r ∈ ℚ, m maximal) as (r·w, m): then
# u^e = (r w)^(e m) for real x wherever u^e is real (an odd power keeps the sign of r w).
# Even m is not used: (w²)^(1/2) = |w|. Otherwise (u, 1).
function radicand_power(u::Frac{UPoly{Q}})
    sn, sd = squarefree(u.num), squarefree(u.den)
    ks = Int[k for (_, k) in vcat(sn, sd)]
    isempty(ks) && return (u, 1)
    g = foldl(gcd, ks)
    P = UPoly{Q}
    for m in g:-1:3
        (isodd(m) && g % m == 0) || continue
        r = rat_root(lc(u.num) / lc(u.den), m)
        r === nothing && continue
        W = prod((p^(k ÷ m) for (p, k) in sn); init = one(P))
        Wd = prod((p^(k ÷ m) for (p, k) in sd); init = one(P))
        return (frac(scale(r, W), Wd), m)
    end
    (u, 1)
end

# --- factorisation in ℚ[z] (residue polynomials) ------------------------------------
# Big prime method: the primitive integer form f of a squarefree polynomial is factored modulo
# a prime p > 2·|lc f|·B, B = 2ⁿ‖f‖₂ (Mignotte: a bound on the coefficients of any factor), by
# Cantor–Zassenhaus; the factors over ℤ are the products of modular ones (times lc f, in the
# symmetric range), found by trying subsets in order of size. Every factor returned divides f
# exactly; only their irreducibility rests on p being prime (Miller–Rabin), and callers never
# depend on it for correctness (a reducible factor is merely handled less well).

# polynomials over 𝔽ₚ: Vector{BigInt}, low -> high, entries in [0, p), no top zeros
function fp_norm(a::Vector{BigInt}, p::BigInt)
    b = BigInt[mod(c, p) for c in a]
    while !isempty(b) && iszero(b[end])
        pop!(b)
    end
    b
end
fp_sub(a, b, p) = fp_norm(BigInt[(i <= length(a) ? a[i] : big(0)) - (i <= length(b) ? b[i] : big(0))
                                 for i in 1:max(length(a), length(b))], p)
function fp_mul(a, b, p)
    (isempty(a) || isempty(b)) && return BigInt[]
    c = zeros(BigInt, length(a) + length(b) - 1)
    for i in eachindex(a), j in eachindex(b)
        c[i + j - 1] += a[i] * b[j]
    end
    fp_norm(c, p)
end
function fp_divrem(a, b, p)
    q = zeros(BigInt, max(length(a) - length(b) + 1, 0))
    li = invmod(b[end], p)
    while length(a) >= length(b)
        c = mod(a[end] * li, p)
        s = length(a) - length(b)
        q[s + 1] = c
        a = copy(a)
        for k in eachindex(b)
            a[s + k] -= c * b[k]
        end
        a = fp_norm(a, p)
    end
    fp_norm(q, p), a
end
fp_monic(a, p) = isempty(a) ? a : fp_norm(a .* invmod(a[end], p), p)
function fp_gcd(a, b, p)
    while !isempty(b)
        a, b = b, fp_divrem(a, b, p)[2]
    end
    fp_monic(a, p)
end
function fp_powmod(a, e::BigInt, f, p)
    r = BigInt[1]
    a = fp_divrem(a, f, p)[2]
    while e > 0
        isodd(e) && (r = fp_divrem(fp_mul(r, a, p), f, p)[2])
        e >>= 1
        e > 0 && (a = fp_divrem(fp_mul(a, a, p), f, p)[2])
    end
    r
end

function is_probable_prime(n::BigInt)
    n < 2 && return false
    small = (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53)
    for q in small
        n % q == 0 && return n == q
    end
    d, s = n - 1, 0
    while iseven(d)
        d >>= 1
        s += 1
    end
    for a in small
        x = powermod(big(a), d, n)
        (x == 1 || x == n - 1) && continue
        composite = true
        for _ in 1:(s - 1)
            x = mod(x * x, n)
            if x == n - 1
                composite = false
                break
            end
        end
        composite && return false
    end
    true
end

# distinct-degree factorisation of a monic squarefree f: [(g, d)], g the product of the
# irreducible factors of degree d
function fp_ddf(f, p)
    out = Tuple{Vector{BigInt},Int}[]
    xp = BigInt[0, 1]
    w = xp
    d = 0
    while length(f) - 1 >= 2 * (d + 1)
        d += 1
        w = fp_powmod(w, p, f, p)                       # x^(p^d) mod f
        g = fp_gcd(f, fp_sub(w, xp, p), p)
        if length(g) > 1
            push!(out, (g, d))
            f = fp_divrem(f, g, p)[1]
            w = fp_divrem(w, f, p)[2]
        end
    end
    length(f) > 1 && push!(out, (f, length(f) - 1))
    out
end

# equal-degree splitting (p odd) of a monic g whose irreducible factors all have degree d;
# the "random" elements come from a fixed LCG, so results are reproducible
function fp_edf(g, d::Int, p, seed::Ref{BigInt})
    n = length(g) - 1
    n == d && return [g]
    e = (p^d - 1) ÷ 2
    while true
        a = BigInt[]
        for _ in 1:n
            seed[] = mod(seed[] * 6364136223846793005 + 1442695040888963407, big(2)^128)
            push!(a, mod(seed[] >> 32, p))
        end
        a = fp_norm(a, p)
        length(a) <= 1 && continue
        c = fp_gcd(g, fp_sub(fp_powmod(a, e, g, p), BigInt[1], p), p)
        1 < length(c) < length(g) &&
            return vcat(fp_edf(c, d, p, seed), fp_edf(fp_divrem(g, c, p)[1], d, p, seed))
    end
end

combos(r::UnitRange{Int}, k::Int) =
    k == 0 ? [Int[]] : [vcat(i, c) for i in r for c in combos((i + 1):last(r), k - 1)]

# monic irreducible factors of a squarefree f ∈ ℚ[z] (product = monic(f))
function factor_Q(f::UPoly{Q})
    degree(f) <= 1 && return [monic(f)]
    l = reduce(lcm, denominator.(f.c))
    F = BigInt[numerator(c * l) for c in f.c]
    F = F .÷ reduce(gcd, F)
    n = length(F) - 1
    p = 2 * abs(F[end]) * big(2)^n * (isqrt(sum(c^2 for c in F)) + 1) + 1
    while true
        p += 1
        is_probable_prime(p) || continue
        fm = fp_monic(fp_norm(F, p), p)
        dfm = fp_norm(BigInt[k * fm[k + 1] for k in 1:n], p)
        length(fp_gcd(fm, dfm, p)) == 1 && break        # squarefree mod p
    end
    seed = Ref(big(20240611))
    mods = Vector{BigInt}[]
    for (g, d) in fp_ddf(fp_monic(fp_norm(F, p), p), p)
        append!(mods, fp_edf(g, d, p, seed))
    end
    out = UPoly{Q}[]
    k = 1
    while 2k <= length(mods)
        hit = nothing
        for S in combos(1:length(mods), k)
            g = BigInt[mod(F[end], p)]
            for i in S
                g = fp_mul(g, mods[i], p)
            end
            g = BigInt[c > p ÷ 2 ? c - p : c for c in g]
            g = g .÷ reduce(gcd, g)
            qq, rr = divrem(UPoly{Q}(Q.(F)), UPoly{Q}(Q.(g)))
            if iszero(rr)
                hit = (S, g, qq)
                break
            end
        end
        if hit === nothing
            k += 1
        else
            S, g, qq = hit
            push!(out, monic(UPoly{Q}(Q.(g))))
            all(c -> isone(denominator(c)), qq.c) || throw(RischError("factor_Q: non-integral cofactor"))
            F = BigInt[numerator(c) for c in qq.c]
            mods = mods[setdiff(1:length(mods), S)]
        end
    end
    push!(out, monic(UPoly{Q}(Q.(F))))
    out
end
