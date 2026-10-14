using Test
import SimpleExpressions
import SymEngine
include("Risch.jl")
using .Risch

# --- exact, package-independent checks of the algebra (no symbolic package needed)
const Q = Rational{BigInt}
const QX = Risch.UPoly{Q}
poly(cs...) = QX(Q[Q(c) for c in cs])      # low -> high
rf(n, d) = Risch.frac(n, d)

@testset "algebra" begin
    p, q = poly(-1, 0, 1), poly(1, 1)                  # x^2-1, x+1
    @test gcd(p, q) == poly(1, 1)
    s, t, g = Risch.gcdex(p, q)
    @test s * p + t * q == g
    @test Risch.squarefree(poly(1, 2, 1) * poly(-1, 1)) ==
          [poly(-1, 1) => 1, poly(1, 1) => 2] ||
          Set(Risch.squarefree(poly(1, 2, 1) * poly(-1, 1))) == Set([poly(-1, 1) => 1, poly(1, 1) => 2])
    @test Risch.rational_roots(poly(-6, 11, -6, 1)) |> sort == Q[1, 2, 3]
    # res_x(x^2 - 1, x - 2) = 3
    @test Risch.resultant(poly(-1, 0, 1), poly(-2, 1)) == Q(3)
end

@testset "rational integrals, verified in the exact field" begin
    cases = [
        (rf(poly(1), poly(0, 1)),                       1, 0),   # 1/x           -> log
        (rf(poly(1), poly(-1, 0, 1)),                   2, 0),   # 1/(x^2-1)     -> 2 logs
        (rf(poly(1), poly(1, 0, 1)),                    0, 1),   # 1/(x^2+1)     -> atan
        (rf(poly(0, 0, 0, 1), poly(1, 0, 1)^2),         1, 0),   # x^3/(x^2+1)^2
        (rf(poly(1), poly(0, 0, 1) * poly(1, 1)),       2, 0),   # 1/(x^2 (x+1))
        (rf(poly(1, 2, 3, 4), poly(1, 1)^3),            1, 0),   # Hermite, triple pole
        (rf(poly(0, 0, 0, 0, 1), poly(-1, 1)),          1, 0),   # polynomial part
    ]
    for (f, nlogs, natans) in cases
        res = Risch.integrate_rational(f)
        @test isempty(res.unresolved)
        @test Risch.derivative_of(res) == f
        @test length(res.logs) >= nlogs - (nlogs > 1 ? 1 : 0)
        @test length(res.atans) == natans
    end
    # irrational residues are reported, not mis-integrated
    res = Risch.integrate_rational(rf(poly(1), poly(2, 0, 0, 0, 1)))   # 1/(x^4+2)
    @test !isempty(res.unresolved)
end

@testset "RootSum: residues of degree > 2, verified in the exact field" begin
    for f in (rf(poly(1), poly(2, 0, 0, 0, 1)),                       # 1/(x⁴+2): needs 2^(1/4)
              rf(poly(1), poly(1, 1, 0, 1)),                          # 1/(x³+x+1)
              rf(poly(0, 1), poly(1, 1, 0, 1)^2),                     # x/(x³+x+1)²  (Hermite part too)
              rf(poly(1), poly(-2, 0, 0, 1) * poly(-3, 0, 0, 1)),     # 1/((x³-2)(x³-3))
              rf(poly(1), poly(3, 0, 1) * poly(2, 0, 0, 0, 1)),       # 1/((x²+3)(x⁴+2))
              rf(poly(1), poly(1, 1, 0, 0, 0, 1)))                    # 1/(x⁵+x+1)
        res = Risch.integrate_rational(f)
        @test !isempty(res.unresolved)
        rss = vcat([Risch.root_sums(rest, R, D, "x") for (rest, R, D) in res.unresolved]...)
        el = Risch.RationalIntegral(res.rational, res.logs, res.atans, Any[], res.quads)
        @test Risch.derivative_of(el) + sum(Risch.rootsum_derivative(rs) for rs in rss) == f
    end
    # dynamic evaluation: m = (z-1)(z-2) splits on the zero divisor z - 1
    m = poly(2, -3, 1)
    a = [poly(2), poly(-3), poly(1)]                                   # (x-1)(x-2)
    b = [poly(0), poly(-1, 1)]                                         # (z-1)·x
    out = Risch.d5_gcd(m, a, b)
    @test Set((Risch.degree(mm), length(W) - 1) for (mm, W) in out) == Set([(1, 2), (1, 0)])
    @test any(p -> p[1] == poly(-1, 1) && p[2] == a, out)              # z = 1: b ≡ 0, gcd = a
    @test Risch.power_sums(poly(-1, 0, 0, 1)) == Q[3, 0, 0]            # z³ - 1
    @test Risch.power_sums(poly(2, -3, 1)) == Q[2, 3]                  # roots 1, 2
    # quadratic residue factors are split off over ℚ: only the quartic is left for RootSum
    res = Risch.integrate_rational(rf(poly(1), poly(3, 0, 1) * poly(2, 0, 0, 0, 1)))
    @test [Risch.degree(u[1]) for u in res.unresolved] == [4]
    @test !isempty(res.quads) || !isempty(res.atans)
    res = Risch.integrate_rational(rf(poly(1), poly(4, 0, 0, 0, 1)))  # 1/(x⁴+4): fully elementary
    @test isempty(res.unresolved) && Risch.check_result(res, rf(poly(1), poly(4, 0, 0, 0, 1)))
end

@testset "real form of quartic RootSums (R2)" begin
    y = poly(-1, 1)
    D4 = y^4 + poly(6) * y^2 + poly(1)                                 # (x-1)⁴ + 6(x-1)² + 1
    for f in (rf(poly(1), poly(1, 0, 0, 0, 1)),                       # 1/(x⁴+1): ℚ(√2)
              rf(poly(1, 1), poly(1, 0, 0, 0, 1)),                    # (x+1)/(x⁴+1)
              rf(poly(1), poly(1, 0, 0, 0, 1)^2),                     # 1/(x⁴+1)²
              rf(poly(1), poly(9, 0, 0, 0, 1)),                       # 1/(x⁴+9): ℚ(√6)
              rf(poly(1), poly(1, 0, -1, 0, 1)),                      # 1/(x⁴-x²+1): ℚ(√3)
              rf(poly(1), poly(-1, 0, 0, 0, 0, 0, 0, 0, 1)),          # 1/(x⁸-1)
              rf(poly(0, 1) * Risch.deriv(D4), D4))                   # residues 1 ± i(1 ± √2): pair sum rational
        res = Risch.integrate_rational(f)
        @test isempty(res.unresolved)
        @test any(q -> q isa Risch.RationalIntegral, res.quads)
        @test Risch.check_result(res, f)
    end
    # roots not in ℚ(i, √d): stays a RootSum
    @test !isempty(Risch.integrate_rational(rf(poly(1), poly(2, 0, 0, 0, 1))).unresolved)
    @test !isempty(Risch.integrate_rational(rf(poly(1), poly(1, 0, 0, 0, 0, 1))).unresolved)   # 1/(x⁵+1)
end

@testset "Rioboo's LogToAtan: atans of polynomials" begin
    datan(u) = Risch.dx(u) / (one(u) + u * u)                          # d/dx atan(u)
    for (A, B) in ((poly(0, -3, 0, 1), poly(-2, 0, 1)),                # Bronstein's example
                   (poly(1, 2, 0, 1), poly(3, 1)), (poly(-1, 0, 1), poly(0, 0, 0, 2)))
        ps = Risch.log_to_atan(A, B)
        @test sum(datan(rf(p, poly(1))) for p in ps) == datan(rf(A, B))
    end
    # B = √e V without adjoining √e:  Σ uⱼ'/(1 + e uⱼ²) = (U'V - UV')/(U² + eV²)
    for (U, V, e) in ((poly(-3, 0, 1), poly(0, 1), 2), (poly(1, 2, 0, 1), poly(3, 1), 5),
                      (poly(0, 0, 0, 1), poly(1), 3), (poly(2, 1), poly(1, 0, 1), 7))
        us = Risch.log_to_atan_sqrt(U, V, Q(e))
        lhs = sum(rf(Risch.deriv(u), poly(1) + poly(e) * u * u) for u in us)
        @test lhs == rf(Risch.deriv(U) * V - U * Risch.deriv(V), U * U + poly(e) * V * V)
    end
    @test Risch.log_to_atan(poly(0, -3, 0, 1), poly(-2, 0, 1)) ==
          [poly(0, 1 // 2, 0, -3 // 2, 0, 1 // 2), poly(0, 0, 0, 1), poly(0, 1)]
    # every atan argument is a polynomial (no jumps at the poles of U/V)
    for f in (rf(poly(6, 0, -3, 0, 1), poly(4, 0, 5, 0, -5, 0, 1)),     # residues ±i, W cubic
              rf(poly(-3, 0, -1), poly(9, 0, -4, 0, 1)))               # residues ±i/√2·…: QuadAtan
        res = Risch.integrate_rational(f)
        @test Risch.check_result(res, f)
        @test all(a -> isone(a[2].den), res.atans)
        @test all(q -> !(q isa Risch.QuadAtan) || isone(q.u.den), res.quads)
        @test !isempty(res.atans) || any(q -> q isa Risch.QuadAtan, res.quads)
    end
end

@testset "factorisation over ℚ" begin
    for (f, degs) in ((poly(1, 0, 0, 0, 1), [4]),                      # z⁴+1 irreducible
                      (poly(4, 0, 0, 0, 1), [2, 2]),                   # Sophie Germain
                      (poly(6, 0, 5, 0, 1), [2, 2]),
                      (poly(-1, 0, 0, 0, 0, 0, 1), [1, 1, 2, 2]),      # z⁶-1
                      (poly(1, 1, 0, 0, 0, 1), [2, 3]),                # z⁵+z+1
                      (poly(1 // 3, 0, 2, 0, 0, 7 // 2), [5]),
                      (poly(-2, 0, 0, 1) * poly(-3, 0, 0, 1), [3, 3]))
        fs = Risch.factor_Q(f)
        @test prod(fs) == Risch.monic(f)
        @test sort(Risch.degree.(fs)) == degs
    end
end

# --- the same terms through each symbolic package
fd(f, a; h = 1e-6) = (f(a + h) - f(a - h)) / (2h)

function run_tests(x, evalat, name)
    @testset "$name" begin
        for f in (1/x, 1/(x^2 - 1), 1/(x^2 + 1), x^3/(x^2 + 1)^2,
                  (x^2 + 1)/(x*(x + 1)^2), 3x^2 + 2x + 1, 1/(x^2*(x + 1)))
            F = Risch.risch_integrate(f, x)
            for a in (1.7, 2.6, 4.1)
                @test isapprox(fd(t -> evalat(F, t), a), evalat(f, a); rtol = 1e-5)
            end
        end
        # exp(x) was refused when this file was written (Stage 1); since Stage 4 it integrates
        let f = exp(x), F = Risch.risch_integrate(exp(x), x)
            for a in (1.7, 2.6, 4.1)
                @test isapprox(fd(t -> evalat(F, t), a), evalat(f, a); rtol = 1e-5)
            end
        end
        # quartic residues with roots in ℚ(i, √d): real form with √d (R2)
        for f in (1/(x^4 + 1), (x + 1)/(x^4 + 1), 1/(x^4 + 9), 1/(x^4 - x^2 + 1), 1/(x^8 - 1))
            F = Risch.risch_integrate(f, x)
            @test !(F isa Risch.IntegralWithRootSums)
            @test occursin("sqrt", string(F))
            for a in (1.7, 2.6, 4.1)
                @test isapprox(fd(t -> evalat(F, t), a), evalat(f, a); rtol = 1e-5)
            end
        end
        # residues algebraic of degree > 2: elementary part + RootSums (verified exactly
        # inside), evaluated numerically by F(a)
        for f in (1/(x^4 + 2), 1/(x^3 + x + 1), x/(x^3 + x + 1), 1/(x^3 + x + 1)^2,
                  1/(x^5 + x + 1), (x^2 + 1)/(x^6 + x + 1), 1/((x^2 + 3)*(x^4 + 2)))
            F = Risch.risch_integrate(f, x)
            @test F isa Risch.IntegralWithRootSums
            @test occursin("RootSum", string(F))
            for a in (0.3, 1.7, 2.6)
                @test isapprox(fd(F, a), evalat(f, a); rtol = 1e-5)
            end
        end
        # a RootSum in a substitution variable (t = sqrt(1 + x), Euler's t) is evaluated through x
        for f in (1/((x^2 + 1)*sqrt(x + 1)), 1/((x^3 + x + 1)*sqrt(x^2 + 1)))
            F = Risch.risch_integrate(f, x)
            @test F isa Risch.IntegralWithRootSums
            for a in (0.3, 1.7, 2.6)
                @test isapprox(fd(F, a), evalat(f, a); rtol = 1e-5)
            end
        end
        # atans of polynomials (Rioboo): the antiderivative is continuous across the zeros of V
        for f in ((x^4 - 3x^2 + 6)/(x^6 - 5x^4 + 5x^2 + 4), (-x^2 - 3)/(x^4 - 4x^2 + 9))
            F = Risch.risch_integrate(f, x)
            vals = [evalat(F, a) for a in -3:0.01:3]
            @test maximum(abs.(diff(vals))) < 0.1
            for a in (-2.2, 0.3, 1.7)
                @test isapprox(fd(t -> evalat(F, t), a), evalat(f, a); rtol = 1e-5)
            end
        end
        # real forms inside towers: R2 terms as tower terms (T1), LogToAtan at a tower level (T2)
        for (f, r) in ((exp(x) + 1/(x^4 + 1), 0.3:0.5:2.8), (log(x) + 1/(x^4 + 1), 1.3:0.5:2.8),
                       (exp(x)*(x^2 + 1) + 1/(x^4 - x^2 + 1), 0.3:0.5:2.8),
                       (exp(x)*(-exp(2x) - 3)/(exp(4x) - 4exp(2x) + 9), -1:0.01:2),
                       ((-log(x)^2 - 3)/(x*(log(x)^4 - 4log(x)^2 + 9)), 1.05:0.02:8),
                       ((log(x)^4 - 3log(x)^2 + 6)/(x*(log(x)^6 - 5log(x)^4 + 5log(x)^2 + 4)), 1.05:0.02:8))
            F = Risch.risch_integrate(f, x)
            @test !occursin("sqrt(1)", string(F))
            step(r) < 0.1 && @test maximum(abs.(diff([evalat(F, a) for a in r]))) < 0.5   # no ±π jumps
            for a in r[[2, end - 1]]
                @test isapprox(fd(t -> evalat(F, t), a), evalat(f, a); rtol = 1e-5)
            end
        end
        @test_throws Risch.NotElementary Risch.risch_integrate(log(x)/(x^4 + 1), x)   # dilogarithm
        # real form of quartic residues at a tower level (step RF): √d log/atan, no jumps
        for (f, r) in ((1/(x*(log(x)^4 + 1)), 1.05:0.01:8), ((log(x) + 1)/(x*(log(x)^4 + 1)), 1.05:0.01:8),
                       (1/(x*(log(x)^4 + 1)^2), 1.05:0.01:8), (1/(x*(log(x)^4 + 9)), 1.05:0.01:8),
                       (exp(x)/(exp(4x) + 1), -2:0.01:2), (exp(x)/(exp(4x) - exp(2x) + 1), -2:0.01:2),
                       (1/(x*log(x)*(log(log(x))^4 + 1)), 1.5:0.01:8))
            F = Risch.risch_integrate(f, x)
            @test !(F isa Risch.IntegralWithRootSums)
            @test occursin("sqrt", string(F))
            @test maximum(abs.(diff([evalat(F, a) for a in r]))) < 0.1
            for a in r[[11, end - 10]]
                @test isapprox(fd(t -> evalat(F, t), a), evalat(f, a); rtol = 1e-5)
            end
        end
        # RootSums inside towers (step RT): at a log or exp level, nested, and base-level ones in a
        # tower; exp levels with Tr(α) ≠ 0 need the correction -Tr(α)·deg W·u
        for f in (1/(x*(log(x)^4 + 2)), 1/(x*(log(x)^3 + log(x) + 1)), (log(x)^2)/(x*(log(x)^3 + log(x) + 1)^2),
                  1/(exp(3x) + exp(x) + 1), exp(2x)/(exp(3x) + exp(x) + 1), 1/(exp(3x) + 2exp(2x) + 1),
                  1/(x*log(x)*(log(log(x))^3 + log(log(x)) + 1)),
                  exp(x) + 1/(x^3 + x + 1), (exp(x) + 1)/(exp(3x) + exp(x) + 1) + 1/(x^3 - 2))
            F = Risch.risch_integrate(f, x)
            @test F isa Risch.IntegralWithRootSums
            @test occursin("RootSum", string(F))
            for a in (1.7, 2.6, 3.4)
                @test isapprox(fd(F, a), evalat(f, a); rtol = 1e-5)
            end
        end
    end
end

simple_x = let; SimpleExpressions.@symbolic x; x; end
sym_x = let; SymEngine.@vars x; x; end
run_tests(simple_x, (e, a) -> e isa Function ? e(a) : e, "SimpleExpressions")
# SymEngine may evaluate a real answer (atan, log with sqrt(2) inside) with a roundoff-size
# imaginary part; drop only that (as `trig_sym_eval` in test_trig.jl)
function risch_sym_eval(e, a)
    z = SymEngine.N(SymEngine.subs(e, sym_x => a))
    z isa Complex || return Float64(z)
    w = ComplexF64(z)
    abs(imag(w)) <= 1e-10 * max(1.0, abs(w)) ? real(w) : w
end
run_tests(sym_x, risch_sym_eval, "SymEngine")
