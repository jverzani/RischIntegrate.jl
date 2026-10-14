using Test
import SimpleExpressions
import SymEngine
import SpecialFunctions
include("Risch.jl")
using .Risch

fd(f, a; h = 1e-6) = (f(a + h) - f(a - h)) / (2h)

# whether the symbolic package defines the SpecialFunctions used in answers (Step 8a)
tt_special_ok(x) = try
    SpecialFunctions.sinint(x); SpecialFunctions.cosint(x)
    true
catch
    false
end

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

    @testset "$name: trigonometric integrands through exp(i·u) towers over ℚ(i) (Step 7)" begin
        fs = (1 / (2 + cos(x)),                    # residues ±i/√3: a pair over ℚ(i)(√3)
              1 / (1 + cos(x)^2),                  # residues ±i/(2√2): ℚ(i)(√2)
              1 / (5 + 4cos(x)),                   # residues ±i/3 ∈ ℚ(i): atan form
              tan(x),                              # -log|cos x| via log(w σw)/2
              tan(x)^2,                            # tan x - x
              1 / cos(x),                          # log|sec x + tan x|
              cos(x) / sin(x),                     # log sin x
              cos(x) / (2 + sin(x)),
              sin(x) / (1 + cos(x)),
              sin(x) * cos(x) / (1 + sin(x)^2),    # log(1 + sin² x)/2: residues 1/2 of a quartic
              sin(x + 1),                          # θ = exp(i(x+1)) alone: no new constant
              x * sin(x + 1),
              sin(x) * log(x) + (1 - cos(x)) / x,  # (1 - cos x) log x: tower [exp(ix), log x]
              # the constant τ = e^i (step 7, part 3): sin(x+1) = (τθ - 1/(τθ))/(2i), θ = exp(ix)
              sin(x) + sin(x + 1),
              sin(x) * cos(x + 1),
              x * cos(x + 1) + sin(x),
              cos(x + 1//2) + sin(x),              # τ = e^(i/2)
              exp(x + 1) * sin(x) + sin(x + 1),    # real constant e (via exp(x+1)) and τ together
              x * cos(1) + sin(x))                 # cos 1 as a constant (SymEngine keeps it symbolic)
        for f in fs
            F = Risch.risch_integrate(f, x)
            for a in (0.7, 1.6, 2.4)
                @test isapprox(fd(t -> evalat(F, t), a), evalat(f, a); rtol = 1e-5, atol = 1e-8)
            end
        end
    end

    @testset "$name: sine and cosine integrals (Step 8a)" begin
        if tt_special_ok(x)
            fs = (sin(x) / x,                      # Si(x): Ei(±ix) in real form
                  cos(x) / x,                      # Ci(x)
                  sin(2x) / x,                     # Si(2x)
                  (1 + cos(x)) / x,                # log x + Ci(x)
                  sin(x)^2 / x,                    # log(x)/2 - Ci(2x)/2
                  sin(x) / (x + 1),                # shift t = -i: cos 1, sin 1 coefficients
                  x * cos(x) / (x + 1)^2)          # Hermite-type reduction, then Si/Ci of x + 1
            for f in fs
                F = Risch.risch_integrate(f, x)
                for a in (0.7, 1.6, 2.4)
                    @test isapprox(fd(t -> evalat(F, t), a), evalat(f, a); rtol = 1e-5, atol = 1e-8)
                end
            end
        else
            @test_skip "SpecialFunctions (sinint, cosint) are not defined for $(typeof(x))"
        end
    end

    @testset "$name: decided non-elementary / outside the supported class" begin
        @test_throws Risch.NotElementary Risch.risch_integrate(sin(x^2), x)          # Fresnel: no real form
        @test_throws Risch.NotElementary Risch.risch_integrate(exp(x) * sin(x) / x, x)   # Ei((1+i)x)
        # ∫ x sin x log x = log x (sin x - x cos x) + cos x - Si(x): an answer when found (the tower
        # order follows the package's term order), else a decision or a refusal
        r = try Risch.risch_integrate(x * sin(x) * log(x), x) catch e; e end
        if r isa Exception
            @test r isa Risch.NotElementary || r isa Risch.RischNotImplemented ||
                  (r isa MethodError && !tt_special_ok(x))
        else
            for a in (0.7, 1.6, 2.4)
                @test isapprox(fd(t -> evalat(r, t), a), evalat(x * sin(x) * log(x), a); rtol = 1e-5, atol = 1e-8)
            end
        end
        # exp(i log 2) = 2^i is not of the form e^(a + bi); SimpleExpressions turns log(2) into a float,
        # refused as an inexact constant
        @test_throws Risch.RischNotImplemented Risch.risch_integrate(sin(x) + sin(x + log(2)), x)
        @test_throws Risch.RischNotImplemented Risch.risch_integrate(sqrt(sin(x)), x)         # algebraic
    end

    # step TC: real forms with atans of polynomials in tan(u/2) plus a linear correction, so the
    # answers are continuous for all real x and F(b) - F(a) is the definite integral (Simpson)
    @testset "$name: continuous trigonometric antiderivatives (step TC)" begin
        tc_simpson(g, a, b; n = 2000) = (h = (b - a) / n;
            h / 3 * (g(a) + g(b) + sum((isodd(k) ? 4 : 2) * g(a + k * h) for k in 1:(n - 1))))
        for f in (1/(2 + cos(x)), 1/(5 + 3sin(x)), cos(x)/(2 + sin(x)^2), 1/(1 + sin(x)^2),
                  1/(3 + sin(2x)), 1/(2 + cos(x))^2, 1/(1 + cos(x)^2), 1/(2 + cos(x/3)))
            F = Risch.risch_integrate(f, x)
            @test occursin("tan", string(F))
            @test maximum(abs.(diff([evalat(F, a) for a in -7:0.02:13]))) < 0.05
            @test isapprox(evalat(F, 13) - evalat(F, -7), tc_simpson(t -> evalat(f, t), -7, 13); atol = 1e-8)
        end
        # the textbook form: (2/√3) atan(tan(x/2)/√3) plus the correction x/√3 - (2/√3) atan(tan(x/2))
        F = Risch.risch_integrate(1/(2 + cos(x)), x)
        @test count("atan", string(F)) == 2
    end

    # step TS: Bioche's rules (s = cos u, sin u, tan u) give the short classical forms; still
    # continuous, with the jump correction u - atan(tan u) for s = tan u
    @testset "$name: simpler trigonometric forms by Bioche's rules (step TS)" begin
        ts_simpson(g, a, b; n = 2000) = (h = (b - a) / n;
            h / 3 * (g(a) + g(b) + sum((isodd(k) ? 4 : 2) * g(a + k * h) for k in 1:(n - 1))))
        for (f, s, natan) in ((cos(x)/(2 + sin(x)^2), "sin", 1), (sin(x)/(2 + cos(x)), "cos", 0),
                              (sin(x)^3/(1 + cos(x)^2), "cos", 1), (cos(x)^3/(2 + sin(x)), "sin", 0),
                              (sin(x)/(cos(x) - 2), "cos", 0), (sin(x)/(3 - cos(x)^2), "cos", 0),
                              (1/(1 + sin(x)^2), "tan", 2), (1/(sin(x)^2 + 4cos(x)^2), "tan", 2),
                              (1/(1 + 3cos(x/3)^2), "tan", 2))
            F = Risch.risch_integrate(f, x)
            str = string(F)
            @test occursin(s, str) && !occursin("tan(x / 2)", str) && !occursin("tan((1/2)*x)", str)
            @test count("atan", str) == natan
            @test maximum(abs.(diff([evalat(F, a) for a in -7:0.02:13]))) < 0.05
            @test isapprox(evalat(F, 13) - evalat(F, -7), ts_simpson(t -> evalat(f, t), -7, 13); atol = 1e-8)
        end
        # step TR: residues of degree > 2 give a RootSum over ℚ in s = sin u or cos u (no `im`),
        # continuous through F(a) (step RN)
        for (f, s) in ((cos(x)/(sin(x)^4 + 2), "sin"), (sin(x)/(cos(x)^5 + 2), "cos"),
                       (cos(x)/(sin(x)^3 + sin(x) + 3), "sin"), (cos(x)/(sin(x)^3 + 2)^2, "sin"))
            F = Risch.risch_integrate(f, x)
            @test F isa Risch.IntegralWithRootSums
            @test all(rs -> rs isa Risch.RootSum && occursin(s, rs.var), F.rootsums)
            @test !occursin("im", string(F))
            @test maximum(abs.(diff([F(a) for a in -7:0.05:13]))) < 0.1
            @test isapprox(F(13) - F(-7), ts_simpson(t -> evalat(f, t), -7, 13); atol = 1e-8)
        end
        # s = tan u with a RootSum: the jump at tan u = ±∞ has no closed form, so the ℚ(i) route
        F = Risch.risch_integrate(1/(sin(x)^4 + 2cos(x)^4), x)
        @test F isa Risch.IntegralWithRootSums && all(rs -> rs isa Risch.TermRootSum, F.rootsums)
        # real poles (cot x): the general route, whose logs are valid on both sides of a pole
        F = Risch.risch_integrate(cos(x)/sin(x), x)
        for a in (-2.0, -0.5, 0.7, 2.5)
            @test isapprox(fd(t -> evalat(F, t), a), evalat(cos(x)/sin(x), a); rtol = 1e-5)
        end
    end
end

simple_x = let; SimpleExpressions.@symbolic x; x; end
sym_x = let; SymEngine.@vars x; x; end
run_tests(simple_x, (e, a) -> e isa Function ? e(a) : e, "SimpleExpressions")
# SymEngine may evaluate a real expression (e.g. atan of a real argument) with a roundoff-size
# imaginary part; drop only that. A genuinely complex value stays complex and fails the comparison.
function trig_sym_eval(e, a)
    z = SymEngine.N(SymEngine.subs(e, sym_x => a))
    z isa Complex || return Float64(z)
    w = ComplexF64(z)
    abs(imag(w)) <= 1e-10 * max(1.0, abs(w)) ? real(w) : w
end
run_tests(sym_x, trig_sym_eval, "SymEngine")
