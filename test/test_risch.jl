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
    res = Risch.integrate_rational(rf(poly(1), poly(1, 0, 0, 0, 1)))   # 1/(x^4+1)
    @test !isempty(res.unresolved)
end

@testset "RootSum: residues of degree > 2, verified in the exact field" begin
    for f in (rf(poly(1), poly(1, 0, 0, 0, 1)),                       # 1/(x⁴+1)
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
        # residues algebraic of degree > 2: elementary part + RootSums (verified exactly
        # inside), evaluated numerically by F(a)
        for f in (1/(x^4 + 1), 1/(x^3 + x + 1), x/(x^3 + x + 1), 1/(x^3 + x + 1)^2,
                  1/(x^5 + x + 1), (x^2 + 1)/(x^6 + x + 1), 1/((x^2 + 3)*(x^4 + 2)))
            F = Risch.risch_integrate(f, x)
            @test F isa Risch.IntegralWithRootSums
            @test occursin("RootSum", string(F))
            for a in (0.3, 1.7, 2.6)
                @test isapprox(fd(F, a), evalat(f, a); rtol = 1e-5)
            end
        end
    end
end

simple_x = let; SimpleExpressions.@symbolic x; x; end
sym_x = let; SymEngine.@vars x; x; end
run_tests(simple_x, (e, a) -> e isa Function ? e(a) : e, "SimpleExpressions")
run_tests(sym_x, (e, a) -> Float64(SymEngine.N(SymEngine.subs(e, sym_x => a))), "SymEngine")
