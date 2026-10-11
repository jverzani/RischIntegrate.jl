using Test
import SimpleExpressions
import SymEngine
include("Risch.jl")
using .Risch

fd(f, a; h = 1e-6) = (f(a + h) - f(a - h)) / (2h)

function run_tests(x, evalat, name)
    @testset "$name: polynomial × exponential × trig" begin
        fs = (sin(x), cos(x),
              x * sin(x), x^2 * cos(2x), x^3 * sin(x / 2),
              sin(x) * cos(x), sin(x)^2, cos(x)^3, sin(2x) * cos(3x),
              exp(x) * sin(x), exp(2x) * cos(3x), x * exp(-x) * sin(x),
              sinh(x) * cos(x), cosh(x)^2, exp(x) + sin(x),
              sin(x)^2 + cos(x)^2,                  # = 1: the cancellation must be exact
              (x + 1)^2 * cos(x))
        for f in fs
            F = Risch.risch_integrate(f, x)
            for a in (0.7, 1.6, 2.4)
                @test isapprox(fd(t -> evalat(F, t), a), evalat(f, a); rtol = 1e-5, atol = 1e-8)
            end
        end
    end

    @testset "$name: outside the supported class (clear errors)" begin
        @test_throws Risch.RischNotImplemented Risch.risch_integrate(sin(x) / x, x)          # Si(x)
        @test_throws Risch.RischNotImplemented Risch.risch_integrate(1 / (2 + cos(x)), x)    # needs the Q(i)-tower
        @test_throws Risch.RischNotImplemented Risch.risch_integrate(tan(x), x)
        @test_throws Risch.RischNotImplemented Risch.risch_integrate(sin(x^2), x)
        @test_throws Risch.RischNotImplemented Risch.risch_integrate(sin(x + 1), x)          # sin 1, cos 1 constants
        @test_throws Risch.RischNotImplemented Risch.risch_integrate(x * sin(x) * log(x), x)
    end
end

simple_x = let; SimpleExpressions.@symbolic x; x; end
sym_x = let; SymEngine.@vars x; x; end
run_tests(simple_x, (e, a) -> e isa Function ? e(a) : e, "SimpleExpressions")
run_tests(sym_x, (e, a) -> Float64(SymEngine.N(SymEngine.subs(e, sym_x => a))), "SymEngine")
