using Test
import SimpleExpressions
import SymEngine
import SpecialFunctions
include("Risch.jl")
using .Risch

fd(f, a; h = 1e-6) = (f(a + h) - f(a - h)) / (2h)

# whether the symbolic package defines the SpecialFunctions used in answers (Step 8a)
ti_special_ok(x) = try
    SpecialFunctions.expinti(x); SpecialFunctions.erf(x); SpecialFunctions.erfi(x)
    true
catch
    false
end

# Compare d/dx F with f on the real parts: where F contains log(w) with w < 0 it is
# complex-valued, but Re F' = (Re F)' is still the right derivative. Complex values
# are reported so the offending integrand can be identified.
function antiderivative_ok(F, f, a, evalat)
    d = fd(t -> evalat(F, t), a)
    v = evalat(f, a)
    if d isa Complex && abs(imag(d)) > 1e-8
        @warn "antiderivative is complex-valued at x = $a" integrand = f antiderivative = F value = d
    end
    isapprox(real(d), real(v); rtol = 1e-5, atol = 1e-8)
end

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
                @test antiderivative_ok(F, f, a, evalat)
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
                @test antiderivative_ok(F, f, a, evalat)
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
                @test antiderivative_ok(F, f, a, evalat)
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
                @test antiderivative_ok(F, f, a, evalat)
            end
        end
    end

    @testset "$name: Risch DE over towers" begin
        fs = (exp(x) * (log(x) + 1/x),                 # exp(x) log(x)
              exp(x) * (log(x)^2 + 2log(x)/x),         # exp(x) log(x)^2
              exp(exp(x)) * exp(x),                    # exp(exp(x))
              exp(exp(x)) * (1 + x * exp(x)),          # x exp(exp(x))
              exp(x) * log(x) + exp(x) / x,            # same as the first, reordered
              exp(x + exp(x)),                         # exp(exp(x)): cancellation exponent i0 = -1
              exp(x + exp(x)) * (1 + exp(x)),          # exp(x + exp(x))
              exp(2x + exp(x)),                        # (exp(x) - 1) exp(exp(x)): i0 = -2
              # cancellation with a non-constant homogeneous solution (step 8b): both were
              # wrongly reported NotElementary before; the answer is exp(exp(x)) = θ/(x t^k)
              exp(x + log(x) + exp(x)) / x,            # s0 = -1, c = 1/x
              exp(2x + log(x) + exp(x)) * exp(-x) / x) # s0 = -2 (SymEngine merges it into the above)
        for f in fs
            F = Risch.risch_integrate(f, x)
            for a in (1.3, 1.9, 2.6)
                @test antiderivative_ok(F, f, a, evalat)
            end
        end
    end

    @testset "$name: non-elementary integrals with SpecialFunctions (Step 8a)" begin
        if ti_special_ok(x)
            fs = (1 / log(x),                      # li(x) = Ei(log x)
                  x / log(x),                      # Ei(2 log x)
                  exp(x^2),                        # √π/2 erfi(x)
                  exp(-x^2),                       # √π/2 erf(x)
                  x^2 * exp(-x^2),                 # -x e^(-x²)/2 + √π/4 erf(x)
                  exp(-x^2 + x),                   # e^(1/4) √π/2 erf(x - 1/2)
                  exp(x) / x,                      # Ei(x)
                  exp(x) / x^2,                    # Ei(x) - e^x/x
                  exp(x) / (x + 1),                # e^(-1) Ei(x + 1)
                  exp(2x) / x,                     # Ei(2x)
                  (x - 1) * exp(x) / x^2 + exp(x) / x,   # e^x/x + Ei(x)
                  exp(1/x),                        # x e^(1/x) - Ei(1/x)
                  exp(exp(x)),                     # Ei(e^x): above the base level
                  exp(x + 1) / x + exp(x))         # e·Ei(x) + e^x: constant field ℚ(e)
            for f in fs
                F = Risch.risch_integrate(f, x)
                for a in (1.3, 1.9, 2.6)
                    @test antiderivative_ok(F, f, a, evalat)
                end
            end
            # ∫ e^x log x = e^x log x - Ei(x): found when log is the top generator (the tower
            # order follows the package's term order); otherwise NotElementary is still correct
            r = try Risch.risch_integrate(exp(x) * log(x), x) catch e; e end
            if r isa Exception
                @test r isa Risch.NotElementary
            else
                @test all(a -> antiderivative_ok(r, exp(x) * log(x), a, evalat), (1.3, 1.9, 2.6))
            end
        else
            @test_skip "SpecialFunctions (expinti, erf, erfi) are not defined for $(typeof(x))"
        end
    end

    @testset "$name: Risch DE with normal denominators in towers (step 9a)" begin
        fs = (exp(exp(x)) * exp(2x) / (exp(x) + 1)^2,                 # exp(e^x)/(e^x + 1)
              exp(exp(x)) * exp(x) * (1 / (exp(x) + 2) - 1 / (exp(x) + 2)^2),   # exp(e^x)/(e^x + 2)
              (1 / (log(x) + 1) - 1 / (x * (log(x) + 1)^2)) * exp(x),           # e^x/(log x + 1)
              exp(sin(x)) * (cos(x) / (2 + cos(x)) + sin(x) / (2 + cos(x))^2)) # exp(sin x)/(2 + cos x), over ℚ(i)
        for f in fs
            F = Risch.risch_integrate(f, x)
            for a in (1.3, 1.9, 2.6)
                @test antiderivative_ok(F, f, a, evalat)
            end
        end
    end

    @testset "$name: Risch DE cancellation cases (step 9b)" begin
        # direct calls of the tower RDE y' + f y = g with t = log x and f = ±1/x = z'/z (z ∈ ℚ(x)):
        # the homogeneous solution 1/z lies in k, so the triangular/degree arguments need z
        T, t = Risch.build_tower(log(x), string(x))
        X = Risch.liftto(T, Risch.frac(Risch.xpoly(Rational{BigInt})), 1)
        one1 = one(t)
        rhs(f, y) = Risch.D(T, 1, y) + f * y
        for (f, y) in ((one1 / X, t * t),                  # Laurent path, (x y)' = x g
                       (-(one1 / X), X * t),               # ∫ z g = log x = t is allowed
                       (one1 / X, one1 / (t + one1)),      # normal denominator, deg b = deg a
                       (-(one1 / X), X * t / (t + one1)))
            g = rhs(f, y)
            r = Risch.rde(T, 1, f, g)
            @test r !== nothing && rhs(f, r) == g
        end
        # no solution: ∫ x · 1/(x²(x+1)) needs log(x + 1), which is not polynomial in t
        @test Risch.rde(T, 1, one1 / X, one1 / (X * X * (X + one1))) === nothing
    end

    @testset "$name: weak normalisation and residue splitting (step 9c)" begin
        T, t = Risch.build_tower(log(x), string(x))
        Qr = Rational{BigInt}
        X0 = Risch.frac(Risch.xpoly(Qr))                  # x at the base
        k0(c) = Risch.kconst(Qr(c))
        X = Risch.liftto(T, X0, 1)
        one1 = one(t)
        # base level, f with simple poles (rde_base used to refuse these)
        for (f, y) in ((k0(2) / X0, X0),                   # residue 2: q = x², then plain integration
                       (one(X0) / (X0 + k0(1)), X0 * X0),  # residue 1 at x = -1
                       (one(X0) / (k0(2) * X0), X0))       # residue 1/2: weakly normalised already
            g = Risch.D(T, 0, y) + f * y
            r = Risch.rde(T, 0, f, g)
            @test r !== nothing && Risch.D(T, 0, r) + f * r == g
        end
        # log level, f with a simple pole at t = log x
        for (f, y) in ((one1 + (2 * one1 / X) / t, t * t),  # residue 2 at t: q = t², then f̃ = 1
                       ((one1 / X) / t, one1))              # residue 1: f̃ = 0, z = log x = t
            g = Risch.D(T, 1, y) + f * y
            r = Risch.rde(T, 1, f, g)
            @test r !== nothing && Risch.D(T, 1, r) + f * r == g
        end
        # residue (Rothstein–Trager) splitting: exponents 1 and 3 on irreducible quadratics
        p1, p2 = X0 * X0 + k0(1), X0 * X0 + X0 + k0(1)
        dp1, dp2 = Risch.D(T, 0, p1), Risch.D(T, 0, p2)
        @test Risch.logderiv_status(T, 0, dp1 / p1 + k0(3) * dp2 / p2) === :yes
        @test Risch.logderiv_status(T, 0, dp1 / p1 + k0(1 // 2) * dp2 / p2) === :no
    end

    @testset "$name: decided non-elementary" begin
        # through the new path: c keeps a normal denominator after step 1, so no solution
        @test_throws Risch.NotElementary Risch.risch_integrate(exp(exp(x)) / (exp(x) + 1), x)
        @test_throws Risch.NotElementary Risch.risch_integrate(log(x) / (x + 1), x)      # dilogarithm
        @test_throws Risch.NotElementary Risch.risch_integrate(1 / (x + log(x)), x)
        @test_throws Risch.NotElementary Risch.risch_integrate(x^x, x)
        @test_throws Risch.NotElementary Risch.risch_integrate(x * exp(x + exp(x)), x)   # needs ∫ exp(exp(x))
        # tower is [exp(x), log(x)]: top monomial log, normal denominator, non-constant residue
        @test_throws Risch.NotElementary Risch.risch_integrate(exp(x) / (x + log(x)), x)
    end

    @testset "$name: quadratic residues inside towers (Stage 5b)" begin
        pts = (1.9, 2.6, 3.3)
        # (integrand, test points): for d > 0 the answer has log((U + √d V)/(U - √d V)), whose
        # argument is negative between the roots of U² - dV²; SimpleExpressions evaluates in
        # Float64, where log of a negative number throws, so those cases use points outside.
        cases = ((1 / (x * (log(x)^2 + 1)), pts),              # atan(log x)
                 (1 / (exp(x) + exp(-x)), pts),                # atan(exp x)
                 (1 / (x * (log(x)^2 + 2)), pts),              # atan(log(x)/√2)/√2
                 (1 / (x * (log(x)^2 - 2)), (4.6, 5.3, 6.1)),  # log((log x - √2)/(log x + √2))/(2√2): log x > √2
                 ((log(x) + 1) / (x * (log(x)^2 + 1)), pts),   # log(log² x + 1)/2 + atan(log x): α ≠ 0
                 (exp(x) / (exp(2x) + 3), pts),                # atan(exp(x)/√3)/√3
                 (exp(x) / (exp(2x) - 2), pts),                # residues ±√2/4, d > 0: exp(x) > √2 here
                 (1 / (exp(2x) + exp(x) + 1), pts),            # α = -1/2, d = -3: exp correction from α
                 (exp(x) + 1 / (x^2 + 2), pts),                # Stage 5a term from the base, inside a tower
                 (x * exp(x) + 1 / (x^2 - 2), pts))            # x > √2 here
        for (f, as) in cases
            F = Risch.risch_integrate(f, x)
            for a in as
                @test antiderivative_ok(F, f, a, evalat)
            end
        end
    end

    @testset "$name: transcendental constants e, log 2, ... (Step 6)" begin
        fs = (exp(x) + exp(x + 1),                     # (1 + e) exp(x)
              x * exp(x + 1) + exp(x),                 # Risch DE over ℚ(e)(x)
              exp(x) * (1 + exp(x + 1)),               # exp(x) + e exp(2x)/2
              exp(x + 1) / (exp(x) + 1),               # residue e: e log(exp(x) + 1)
              exp(x) + exp(x + 1//2),                  # constant generator e^(1/2)
              log(x) + log(2x),                        # 2x log x - 2x + x log 2
              log(x) * log(2x),                        # ∫ log² x + log 2 ∫ log x
              log(2x) - log(x),                        # = log 2: x log 2
              log(x) / x + log(6x) / x,                # log 6 = log 2 + log 3
              2^x,                                     # 2^x / log 2: Risch DE y' + log(2) y = 1
              x * 3^x,
              1 / (x * (log(x) + log(2x))))            # log(2 log x + log 2)/2
        for f in fs
            F = Risch.risch_integrate(f, x)
            for a in (1.3, 1.9, 2.6)
                @test antiderivative_ok(F, f, a, evalat)
            end
        end
    end

    @testset "$name: awaiting later stages" begin
        @test_throws Risch.RischNotImplemented Risch.risch_integrate(1 / (x * (log(x)^4 + 1)), x)  # quartic residues
        @test_throws Risch.RischNotImplemented Risch.risch_integrate(log(x) / (x^2 + 2), x)        # atan × log
    end
end

simple_x = let; SimpleExpressions.@symbolic x; x; end
sym_x = let; SymEngine.@vars x; x; end
run_tests(simple_x, (e, a) -> e isa Function ? e(a) : e, "SimpleExpressions")
run_tests(sym_x, (e, a) -> (z = SymEngine.N(SymEngine.subs(e, sym_x => a));
                            z isa Complex ? ComplexF64(z) : Float64(z)), "SymEngine")
