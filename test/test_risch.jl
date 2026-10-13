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
        # residues that are roots of a quartic are still not representable
        @test_throws Risch.RischNotImplemented Risch.risch_integrate(1/(x^4 + 1), x)
    end
end

simple_x = let; SimpleExpressions.@symbolic x; x; end
sym_x = let; SymEngine.@vars x; x; end
run_tests(simple_x, (e, a) -> e isa Function ? e(a) : e, "SimpleExpressions")
run_tests(sym_x, (e, a) -> Float64(SymEngine.N(SymEngine.subs(e, sym_x => a))), "SymEngine")
