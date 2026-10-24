using Test
import SimpleExpressions
import SymEngine
using RischIntegrate
import RischIntegrate as Risch
@isdefined(ALL_TYPES) || (const ALL_TYPES = true)             # (set in runtests.jl)

# Step 5, first half: ℚ(√d) as a constant field, and change of constant field in towers.
# None of this is used by `risch_integrate` yet; these tests exercise it directly.

const Q = Rational{BigInt}
const S = Risch.QS{2}                       # ℚ(√2)
s(a, b) = S(Q(a), Q(b))
spoly(cs...) = Risch.UPoly{S}(S[c isa S ? c : s(c, 0) for c in cs])   # low -> high
φ(c) = Risch.cfromQ(S, c)

fd(f, a; h = 1e-6) = (f(a + h) - f(a - h)) / (2h)

@testset "ℚ(√2) arithmetic and interface" begin
    u = s(1, 1)                                         # 1 + √2
    @test u * inv(u) == one(S)
    @test u^3 == u * u * u
    @test u^-2 == inv(u * u)
    @test u * 3 == 3 * u == s(3, 3)
    @test Risch.crational(s(5, 0)) == Q(5)
    @test Risch.crational(u) === nothing
    @test Risch.cinteger(s(4, 0)) == Q(4)
    @test Risch.cinteger(s(1 // 2, 0)) === nothing
    @test Risch.cflat_all(S, [u, s(0, 3)]) == [Q[1, 1], Q[0, 3]]
    # square roots: (1+√2)², 2, 8, 9, (2+√2)²
    for x in (s(3, 2), s(2, 0), s(8, 0), s(9, 0), s(6, 4))
        r = Risch.qs_sqrt(x)
        @test r !== nothing && r * r == x
    end
    @test Risch.qs_sqrt(s(3, 0)) === nothing
    @test Risch.qs_sqrt(s(1, 1)) === nothing
    @test Risch.qs_sqrt(s(-1, 0)) === nothing
end

@testset "roots in ℚ(√2)" begin
    roots(p) = Set(Risch.constant_roots(p))
    lin(r) = Risch.UPoly{S}(S[-r, one(S)])                                 # z - r
    @test roots(spoly(-1, -2, 1)) == Set([s(1, 1), s(1, -1)])            # z² - 2z - 1
    @test roots(spoly(-2, 0, 1)) == Set([s(0, 1), s(0, -1)])             # z² - 2
    @test roots(spoly(-1 // 8, 0, 1)) == Set([s(0, 1 // 4), s(0, -1 // 4)])  # residues of 1/(x²-2)
    @test roots(lin(s(3, 0)) * lin(s(1, 1))) == Set([s(3, 0), s(1, 1)])
    @test roots(lin(s(3, 0)) * spoly(-2, 0, 1)) == Set([s(3, 0), s(0, 1), s(0, -1)])
    @test roots(spoly(1, 0, 1)) == Set{S}()                              # z² + 1: none in ℚ(√2)
    @test roots(spoly(-3, 0, 1)) == Set{S}()                             # z² - 3: none in ℚ(√2)
end

# --- Step 6, part 1: the transcendental constant field ℚ(t₁, …, tₖ) ---------------
const E1 = Risch.cfield(1)                  # ℚ(t), t standing for e = exp(1) in the tests below
const et = Risch.tgen(E1, 1)
q(r) = Risch.cfromQ(E1, Q(r))
epoly(cs...) = Risch.UPoly{E1}(E1[c isa E1 ? c : q(c) for c in cs])   # low -> high
flatv(cs...) = Risch.cflat_all(E1, E1[c isa E1 ? c : q(c) for c in cs])

@testset "ℚ(t) arithmetic and interface" begin
    @test Risch.cdepth(E1) == 1 && Risch.cdepth(Risch.cfield(3)) == 3
    @test et * inv(et) == one(E1)
    @test (et + q(1))^2 == et * et + 2 * et + q(1)
    @test Risch.crational(q(3 // 2)) == Q(3 // 2)
    @test Risch.crational(et) === nothing
    @test Risch.crational(et / et) == Q(1)
    @test Risch.crational((et * et - q(1)) / (et - q(1)) - et) == Q(1)
    @test Risch.cinteger(q(4)) == Q(4)
    @test Risch.cinteger(et) === nothing
    # ℚ-linear relations through the flattened coordinates
    v = flatv(et, 2 * et, q(1))
    @test Risch.solve_columns([v[1]], v[2]) == Q[2]
    @test Risch.solve_columns([v[1]], v[3]) === nothing
    w = flatv(inv(et + q(1)), et / (et + q(1)), q(1))   # 1/(t+1) + t/(t+1) = 1
    @test Risch.solve_columns([w[1], w[2]], w[3]) == Q[1, 1]
    @test Risch.solve_columns([w[1]], w[3]) === nothing
    # square roots
    for c in (et * et, (et + q(1))^2 / (4 * et * et), q(9 // 4), (et * et + q(2) * et + q(1)) * et^4)
        r = Risch.csqrt(c)
        @test r !== nothing && r * r == c
    end
    @test Risch.csqrt(et) === nothing
    @test Risch.csqrt(q(2)) === nothing
    @test Risch.csqrt(et * et + q(1)) === nothing
    # two generators are independent indeterminates
    E2 = Risch.cfield(2)
    t1, t2 = Risch.tgen(E2, 1), Risch.tgen(E2, 2)
    @test t1 != t2 && Risch.crational(t1 * t2 / (t2 * t1)) == Q(1)
    u = Risch.cflat_all(E2, [t1, t2, t1 + t2])
    @test Risch.solve_columns([u[1]], u[2]) === nothing
    @test Risch.solve_columns([u[1], u[2]], u[3]) == Q[1, 1]
end

@testset "roots in ℚ(t)" begin
    roots(p) = Set(Risch.constant_roots(p))
    @test roots(epoly(-et * et, 0, 1)) == Set([et, -et])                        # z² - t²
    @test roots(epoly(-inv(4 * et * et), 0, 1)) == Set([inv(2 * et), -inv(2 * et)])  # residues of 1/(x² - t²)
    @test roots(epoly(-3, 1) * epoly(-et * et, 0, 1)) == Set([q(3), et, -et])
    @test roots(epoly(-et / q(2), 1)) == Set([et / q(2)])
    @test roots(epoly(-et, 0, 1)) == Set{E1}()                                  # z² - t: none
    @test roots(epoly(-2, 0, 1)) == Set{E1}()                                   # z² - 2: none
end

# --- Step 7, part 1: ℚ(i), ℚ(i)(√d), ℚ(i)(t) as constant fields; conjugation -----------
const QI = Risch.QI
zi(a, b) = QI(Q(a), Q(b))
ipoly(cs...) = Risch.UPoly{QI}(QI[c isa QI ? c : zi(c, 0) for c in cs])
const I1 = zi(0, 1)

@testset "ℚ(i) arithmetic and interface" begin
    u = zi(1, 2)
    @test u * inv(u) == one(QI) && u^3 == u * u * u && u^-1 == inv(u)
    @test u * 2 == 2 * u == zi(2, 4)
    @test Risch.crational(zi(3, 0)) == Q(3) && Risch.crational(I1) === nothing
    @test Risch.cflat_all(QI, [u, I1]) == [Q[1, 2], Q[0, 1]]
    @test Risch.cconj(u) == zi(1, -2)
    for x in (zi(-1, 0), zi(0, 2), zi(3, 4), zi(-4, 0), zi(9 // 4, 0), zi(-3, 4))
        r = Risch.csqrt(x)
        @test r !== nothing && r * r == x
    end
    @test Risch.csqrt(zi(2, 0)) === nothing
    @test Risch.csqrt(zi(1, 1)) === nothing
    @test Risch.csqrt(zi(-1 // 3, 0)) === nothing
end

@testset "roots in ℚ(i)" begin
    roots(p) = Set(Risch.constant_roots(p))
    lin(r) = Risch.UPoly{QI}(QI[-r, one(QI)])
    @test roots(ipoly(1, 0, 1)) == Set([I1, -I1])                          # z² + 1
    @test roots(ipoly(1 // 4, 0, 1)) == Set([I1 / zi(2, 0), -I1 / zi(2, 0)])  # residues of 1/(x²+1)
    @test roots(lin(zi(1, 1)) * lin(zi(2, 0))) == Set([zi(1, 1), zi(2, 0)])
    @test roots(lin(zi(3, 0)) * ipoly(1, 0, 1)) == Set([zi(3, 0), I1, -I1])
    @test roots(lin(I1) * lin(zi(0, -2))) == Set([I1, zi(0, -2)])
    @test roots(ipoly(1 // 3, 0, 1)) == Set{QI}()                          # ±i/√3 ∉ ℚ(i)
end

@testset "ℚ(i)(√3) and conjugation" begin
    S3 = Risch.QSB{3,QI}
    w(a, b) = S3(a isa QI ? a : zi(a, 0), b isa QI ? b : zi(b, 0))
    @test Risch.QS{3} === Risch.QSB{3,Q}                                    # the old name still works
    v = w(zi(1, 1), zi(0, 2))
    @test v * inv(v) == one(S3) && v^2 == v * v
    @test Risch.crational(w(5, 0)) == Q(5) && Risch.crational(w(I1, 0)) === nothing
    @test Risch.cflat_all(S3, [v]) == [Q[1, 1, 0, 2]]
    @test Risch.cconj(v) == w(zi(1, -1), zi(0, -2))
    for x in (w(-3, 0), w(3, 0), w(zi(0, 2), 0), w(4, 2))                  # -3 = (i√3)², ..., (1+√3)²
        r = Risch.csqrt(x)
        @test r !== nothing && r * r == x
    end
    # residues of 1/(x² + 1/3), z² + 3/4: ±(i/2)√3 ∈ ℚ(i)(√3)
    roots = Set(Risch.constant_roots(Risch.UPoly{S3}(S3[w(3 // 4, 0), zero(S3), one(S3)])))
    @test roots == Set([w(0, zi(0, 1 // 2)), w(0, zi(0, -1 // 2))])
    # conjugation on ℚ(√-3) negates √-3
    @test Risch.cconj(Risch.QS{-3}(Q(1), Q(2))) == Risch.QS{-3}(Q(1), Q(-2))
end

@testset "ℚ(i)(t): constants over a complex base" begin
    F = Risch.cfield(1, QI)
    @test Risch.cdepth(F) == 1 && Risch.cbase(F) === QI && Risch.cbase(Risch.cfield(2)) === Q
    t = Risch.tgen(F, 1)
    k(c) = Risch.cfromQ(F, Q(c))
    ii = Risch.kconst(I1)
    @test Risch.crational(t / t) == Q(1) && Risch.crational(ii) === nothing
    @test Risch.cconj(ii * t) == -ii * t
    roots = Set(Risch.constant_roots(Risch.UPoly{F}(F[t * t, zero(F), one(F)])))    # z² + t²
    @test roots == Set([ii * t, -ii * t])
    r = Risch.csqrt(-4 * t * t)
    @test r !== nothing && r * r == -4 * t * t
end

@testset "integration over ℚ(i): rational functions and an exp(ix) tower, verified exactly" begin
    X = Risch.frac(Risch.xpoly(QI))
    kc(c) = Risch.kconst(c isa QI ? c : zi(c, 0))
    for f in (inv(X * X + kc(1)), X / (X * X + kc(4)), inv(X * X * X + X), inv((X - kc(I1))^2 * (X + kc(2))))
        res = Risch.integrate_rational(f)
        @test isempty(res.unresolved)
        @test Risch.check_result(res, f)
    end
    @test !isempty(Risch.integrate_rational(inv(X * X + kc(1 // 3))).unresolved)   # residues ∉ ℚ(i)
    # θ = exp(ix), built directly (trig parsing is part 2): Dθ = iθ
    T = Risch.Tower(QI, "x", Dict{Int,Int}())
    θ = Risch.make_exp(T, kc(I1) * X)
    @test [lv.kind for lv in T.levels] == [:exp]
    one1 = one(θ)
    lc1(c) = Risch.lconst(T, c isa QI ? c : zi(c, 0), 1)
    Xθ = Risch.liftto(T, X, 1)
    for f in (θ,                                   # exp(ix)
              Xθ * θ,                              # x exp(ix): Risch DE over ℚ(i)(x)
              (θ + inv(θ)) * lc1(1 // 2),          # cos x
              inv(θ + one1),                       # residue i, exp correction
              θ / (θ * θ + lc1(4)),                # residues ±1/4 ... over ℚ(i)
              (θ - inv(θ)) * (θ - inv(θ)))         # (2i sin x)²
        res = Risch.integrate_el(T, 1, f)
        @test Risch.check_tower(T, 1, res, f)
    end
end

function run_tests(x, evalat, name)
    xk = string(x)
    fs = (exp(x), log(x) / x, exp(x) * log(x + 1) / (x^2 + 3), x^x, exp(exp(x)),
          log(log(x)), exp(x / 2) + exp(x), sinh(x) * cosh(x), log(x^2 - 1) + log(x - 1))

    @testset "$name: change_constants commutes with the derivation" begin
        for f in fs
            T, el = Risch.build_tower(f, xk)
            T2 = Risch.change_constants(T, S, φ)
            el2 = Risch.change_constants(T, T2, el, φ)
            @test [lv.kind for lv in T2.levels] == [lv.kind for lv in T.levels]
            @test Risch.ctype(T2) === S
            @test Risch.D(T2, el2) == Risch.change_constants(T, T2, Risch.D(T, el), φ)
            # the same tower built directly over ℚ(√2) gives the same element
            T3, el3 = Risch.build_tower(f, xk; constants = S)
            @test [lv.kind for lv in T3.levels] == [lv.kind for lv in T.levels]
            @test el3 == el2
        end
    end

    @testset "$name: integration over a ℚ(√2) tower, verified exactly" begin
        gs = (log(x), log(x) / x, 1 / (x * log(x)), x * exp(x), exp(x) / (exp(x) + 1),
              exp(x) * (log(x) + 1 / x), 1 / (x^2 - 1))
        for (k, g) in enumerate(gs)
            T, el = Risch.build_tower(g, xk; constants = S)
            L = length(T.levels)
            @test (L > 0) == (k < length(gs))
            if L > 0
                res = Risch.integrate_el(T, L, el)
                @test Risch.check_tower(T, L, res, el)
            else
                res = Risch.integrate_rational(el)
                @test Risch.check_result(res, el)
            end
        end
    end

    @testset "$name: residues in ℚ(√2) and output with sqrt(2)" begin
        # ∫ 1/(x²-2) = (√2/4) log(x - √2) - (√2/4) log(x + √2): rational over ℚ(√2)
        # (g, whether some residue is irrational): residues of x/(x²-2) are both 1/2
        for (g, irr) in ((1 / (x^2 - 2), true), (x / (x^2 - 2), false), ((x + 1) / (x^2 - 2), true))
            T, el = Risch.build_tower(g, xk; constants = S)
            res = Risch.integrate_rational(el)
            @test isempty(res.unresolved)
            @test Risch.check_result(res, el)
            @test any(c -> !iszero(c.b), S[c for (c, _) in res.logs]) == irr
            b = Risch.Builder(Risch.auto_build(g, x), Risch.auto_lift(g, x), x)
            F = Risch.to_term(b, res)
            for a in (2.3, 3.1, 4.7)
                d = fd(t -> evalat(F, t), a)
                @test isapprox(real(d), evalat(g, a); rtol = 1e-5, atol = 1e-8)
            end
        end
    end
end

function run_const_tests(x, evalat, name)
    xk = string(x)
    E = exp(1.0)
    P = Risch.UPoly{E1}
    X = Risch.frac(Risch.xpoly(E1))                   # x ∈ ℚ(t)(x)
    k(c) = Risch.kconst(c isa E1 ? c : q(c))          # constant as an element of ℚ(t)(x)
    builder(gens) = Risch.Builder(Risch.auto_build(x, x), Risch.auto_lift(x, x), x, gens)
    ok(F, g, a) = isapprox(real(fd(t -> evalat(F, t), a)), g(a); rtol = 1e-5, atol = 1e-8)

    @testset "$name: rational integrals over ℚ(t), output with exp(1) and log(2)" begin
        # (integrand over ℚ(t)(x), the same as a Julia function with t = e, test points)
        cases = ((k(et) / X, a -> E / a, (1.7, 2.6)),                            # e log x
                 (inv(X * X - k(et * et)), a -> 1 / (a^2 - E^2), (3.1, 4.2)),    # residues ±1/(2e)
                 (k(et * et) * X + inv(X + k(et)), a -> E^2 * a + 1 / (a + E), (1.7, 2.6)),
                 ((X + k(et)) / (X * X - k(1)), a -> (a + E) / (a^2 - 1), (1.7, 2.6)))   # residues (1 ± t)/2
        for (f, g, pts) in cases
            res = Risch.integrate_rational(f)
            @test isempty(res.unresolved)
            @test Risch.check_result(res, f)
            F = Risch.to_term(builder([Risch.ConstGen(:exp, Q(1))]), res)
            for a in pts
                @test ok(F, g, a)
            end
        end
        # the same field read as ℚ(log 2): ∫ log(2)/x = log(2) log(x)
        res = Risch.integrate_rational(k(et) / X)
        F = Risch.to_term(builder([Risch.ConstGen(:log, Q(2))]), res)
        @test ok(F, a -> log(2.0) / a, 1.7)
    end

    @testset "$name: towers over ℚ(t): Risch DE and residues with constant coefficients" begin
        # (input over ℚ, constant factor in ℚ(t), the product as a Julia function with t = e)
        cases = ((x * exp(x), et, a -> E * a * exp(a)),                  # Risch DE over ℚ(t)(x)
                 (exp(x) / (exp(x) + 1), et * et, a -> E^2 * exp(a) / (exp(a) + 1)),
                 (log(x), inv(et + q(1)), a -> log(a) / (E + 1)),
                 (log(x) / x, et, a -> E * log(a) / a),           # (e/2) log² x: log coefficient c = e
                 (log(x)^2 / x, et, a -> E * log(a)^2 / a),
                 (exp(x) * log(x) + exp(x) / x, et, a -> E * (exp(a) * log(a) + exp(a) / a)))
        for (f, c, g) in cases
            T, el = Risch.build_tower(f, xk; constants = E1)
            push!(T.consts, Risch.ConstGen(:exp, Q(1)))
            L = length(T.levels)
            f2 = el * Risch.lconst(T, c, L)
            res = Risch.integrate_el(T, L, f2)
            @test Risch.check_tower(T, L, res, f2)
            F = Risch.to_term(builder(T.consts), T, res)
            for a in (1.3, 2.1)
                @test ok(F, g, a)
            end
        end
    end
end

simple_x = let; SimpleExpressions.@symbolic x; x; end
sym_x = let; SymEngine.@vars x; x; end
tc_simple_eval = (e, a) -> e isa Function ? e(a) : e
tc_sym_eval = (e, a) -> (z = SymEngine.N(SymEngine.subs(e, sym_x => a));
                      z isa Complex ? ComplexF64(z) : Float64(z))
run_tests(simple_x, tc_simple_eval, "SimpleExpressions")
ALL_TYPES && run_tests(sym_x, tc_sym_eval, "SymEngine")
run_const_tests(simple_x, tc_simple_eval, "SimpleExpressions")
ALL_TYPES && run_const_tests(sym_x, tc_sym_eval, "SymEngine")
