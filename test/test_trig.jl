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

    @testset "$name: decided non-elementary / outside the supported class" begin
        @test_throws Risch.NotElementary Risch.risch_integrate(sin(x) / x, x)        # Si(x)
        @test_throws Risch.NotElementary Risch.risch_integrate(sin(x^2), x)          # Fresnel
        @test_throws Risch.NotElementary Risch.risch_integrate(cos(x) / x, x)        # Ci(x)
        # ∫ x sin x log x needs Si(x); decided by the tower, or refused where its bounds are partial
        @test try
            Risch.risch_integrate(x * sin(x) * log(x), x)
            false
        catch e
            e isa Risch.NotElementary || e isa Risch.RischNotImplemented
        end
        # exp(i log 2) = 2^i is not of the form e^(a + bi); SimpleExpressions turns log(2) into a float,
        # refused as an inexact constant
        @test_throws Risch.RischNotImplemented Risch.risch_integrate(sin(x) + sin(x + log(2)), x)
        @test_throws Risch.RischNotImplemented Risch.risch_integrate(sqrt(sin(x)), x)         # algebraic
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
