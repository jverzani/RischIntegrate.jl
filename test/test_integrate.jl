using Test
import SimpleExpressions
import SymEngine
include("Risch.jl")
using .Risch

fd(f, a; h = 1e-6) = (f(a + h) - f(a - h)) / (2h)

function run_tests(x, evalat, name)
    @testset "$name: elementary integrals in log towers" begin
        fs = (log(x),                       # x log x - x
              log(x)^2,                     # x log^2 x - 2x log x + 2x
              x * log(x),
              (x^2 + 1) * log(x),
              log(x) / x,                   # log^2(x) / 2
              log(x)^2 / x,
              1 / (x * log(x)),             # log(log(x))
              (log(x) + 1) / (x * log(x)),  # log x + log(log x)
              log(x) / (x + 1)^2,           # Hermite in the base, then a log term
              log(x)^3,
              log(x + 1),
              log(x^2 - 1) + log(x - 1))    # two generators
        for f in fs
            F = Risch.risch_integrate(f, x)
            for a in (1.7, 2.6, 4.1)
                @test isapprox(real(fd(t -> evalat(F, t), a)), real(evalat(f, a)); rtol = 1e-5, atol = 1e-8)
            end
        end
    end

    @testset "$name: rational functions of exp (no Risch DE needed)" begin
        fs = (exp(x) / (exp(x) + 1),        # log(exp(x) + 1)
              1 / (exp(x) + 1),             # x - log(exp(x) + 1)
              exp(x) / (exp(x) + 1)^2,
              1 / (exp(x) + 1)^2,
              exp(2x) / (exp(x) + 1)^2,
              (exp(x) + 2) / (exp(x) + 1),
              1 / (exp(x) - 1))
        for f in fs
            F = Risch.risch_integrate(f, x)
            for a in (0.7, 1.6, 2.4)
                @test isapprox(fd(t -> evalat(F, t), a), evalat(f, a); rtol = 1e-5, atol = 1e-8)
            end
        end
    end

    @testset "$name: exp terms via the Risch differential equation" begin
        fs = (exp(x),                        # exp(x)
              x * exp(x),                    # (x - 1) exp(x)
              x^2 * exp(x),
              (x + 1) * exp(x),
              exp(-x),                       # θ^-1 (Laurent term)
              exp(x) * (x - 1) / x^2,        # exp(x)/x
              exp(1/x) / x^2,                # -exp(1/x)
              2x * exp(x^2),                 # exp(x^2)
              x * exp(x^2),
              exp(2x) + exp(x),
              sinh(x),                       # cosh(x)
              x * exp(x) + exp(x) / (exp(x) + 1),     # RDE part + log part together
              (x^2 + 1) * exp(-x))
        for f in fs
            F = Risch.risch_integrate(f, x)
            for a in (0.7, 1.6, 2.4)
                @test isapprox(fd(t -> evalat(F, t), a), evalat(f, a); rtol = 1e-5, atol = 1e-8)
            end
        end
    end

    @testset "$name: irrational and complex quadratic residues (Stage 5a)" begin
        fs = (1 / (x^2 + x + 1),            # (2/sqrt(3)) atan((2x+1)/sqrt(3))
              x / (x^2 + x + 1),
              (x + 3) / (x^2 + 4x + 7),
              1 / (x^2 + 2),                # atan(x/sqrt(2))/sqrt(2)
              1 / (x^2 - 2),                # log((x - sqrt(2))/(x + sqrt(2)))/(2 sqrt(2))
              1 / (x^2 - x - 1),            # d = 5
              (3x + 1) / (x^2 - 3),
              1 / (x^3 - 1),                # rational residue 1/3 together with a quadratic pair
              1 / (x^2 + x + 1)^2,          # Hermite reduction, then a quadratic pair
              1 / (x^2 + 3))
        for f in fs
            F = Risch.risch_integrate(f, x)
            for a in (2.3, 3.1, 4.7)
                @show fd(t -> evalat(F, t), a), evalat(f, a)
                #@test isapprox(real(fd(t -> evalat(F, t), a)), real(evalat(f, a)); rtol = 1e-5, atol = 1e-8)
            end
        end
    end

    @testset "$name: Risch DE over towers" begin
        fs = (exp(x) * (log(x) + 1/x),                 # exp(x) log(x)
              exp(x) * (log(x)^2 + 2log(x)/x),         # exp(x) log(x)^2
              exp(exp(x)) * exp(x),                    # exp(exp(x))
              exp(exp(x)) * (1 + x * exp(x)),          # x exp(exp(x))
              exp(x) * log(x) + exp(x) / x)            # same as the first, reordered
        for f in fs
            F = Risch.risch_integrate(f, x)
            for a in (1.3, 1.9, 2.6)
                @test isapprox(fd(t -> evalat(F, t), a), evalat(f, a); rtol = 1e-5, atol = 1e-8)
            end
        end
    end

    @testset "$name: decided non-elementary" begin
        @test_throws Risch.NotElementary Risch.risch_integrate(1 / log(x), x)            # li(x)
        @test_throws Risch.NotElementary Risch.risch_integrate(log(x) / (x + 1), x)      # dilogarithm
        @test_throws Risch.NotElementary Risch.risch_integrate(1 / (x + log(x)), x)
        @test_throws Risch.NotElementary Risch.risch_integrate(exp(x^2), x)              # erfi
        @test_throws Risch.NotElementary Risch.risch_integrate(exp(-x^2), x)             # erf
        @test_throws Risch.NotElementary Risch.risch_integrate(exp(x) / x, x)            # Ei(x)
        @test_throws Risch.NotElementary Risch.risch_integrate(exp(x) / x^2, x)
        @test_throws Risch.NotElementary Risch.risch_integrate(exp(1/x), x)
        @test_throws Risch.NotElementary Risch.risch_integrate(exp(x) * log(x), x)       # Ei(x) - ...
        @test_throws Risch.NotElementary Risch.risch_integrate(exp(exp(x)), x)           # Ei(exp(x))
        @test_throws Risch.NotElementary Risch.risch_integrate(x^x, x)
    end

    @testset "$name: awaiting later stages" begin
        @test_throws Risch.RischNotImplemented Risch.risch_integrate(1 / (x * (log(x)^2 + 1)), x)  # atan(log x)
        @test_throws Risch.RischNotImplemented Risch.risch_integrate(1 / (exp(x) + exp(-x)), x)     # atan(exp x)
#        @test_throws Risch.RischNotImplemented Risch.risch_integrate(exp(x) / (x + log(x)), x)      # normal denominator over a tower
    end
end

simple_x = let; SimpleExpressions.@symbolic x; x; end
sym_x = let; SymEngine.@vars x; x; end
run_tests(simple_x, (e, a) -> e isa Function ? e(a) : e, "SimpleExpressions")
run_tests(sym_x, (e, a) -> Float64(SymEngine.N(SymEngine.subs(e, sym_x => a))), "SymEngine")
