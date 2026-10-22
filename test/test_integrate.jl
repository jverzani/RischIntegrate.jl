using Test
import SimpleExpressions
import SymEngine
import SpecialFunctions
using RischIntegrate
import RischIntegrate as Risch
Risch.HYP_ANSWERS[] = false     # the decision tests expect NotElementary (₂F₁ answers: their own testset)

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

    @testset "$name: radicals by substitution (step 10a)" begin
        fs = (sqrt(x), x * sqrt(x), 1 / sqrt(x),
              x^2 * x^(1//3),                      # t = x^(1/3)
              x / sqrt(x + 1),                     # 2(t³/3 - t), t = √(x+1)
              sqrt(x + 1) / x,                     # 2t + log((t-1)/(t+1)): t > 1 here
              1 / (x * sqrt(x - 1)),               # 2 atan(√(x-1))
              sqrt(x) + x^(1//3),                  # n = 6
              1 / (sqrt(x) + 1),                   # 2√x - 2 log(√x + 1)
              sqrt((x + 2) / (x + 1)),             # linear-fractional radicand
              exp(sqrt(x)),                        # 2(√x - 1) e^√x: an exp level over ℚ(t)
              log(sqrt(x)),                        # a log level over ℚ(t)
              sin(sqrt(x)))                        # trig over ℚ(i)(t): 2 sin √x - 2√x cos √x
        for f in fs
            F = Risch.risch_integrate(f, x)
            for a in (1.3, 1.9, 2.6)
                @test antiderivative_ok(F, f, a, evalat)
            end
        end
        F = Risch.risch_integrate(sqrt(x) + sqrt(x + 1) + sqrt(x + 2), x)    # x = t², then two roots (step BQ)
        @test antiderivative_ok(F, sqrt(x) + sqrt(x + 1) + sqrt(x + 2), 2.0, evalat)
        @test_throws Risch.NotElementary Risch.risch_integrate(sqrt(x^3 + 1) + sqrt(x^3 + 2) + sqrt(x^3 + 3), x)  # phase 3a
        @test_throws Risch.NotElementary Risch.risch_integrate(1 / sqrt(x^3 + 1), x)  # elliptic (SI2 phase 1)
        @test_throws Risch.RischNotImplemented Risch.risch_integrate(sqrt(log(x)), x)
        @test_throws Risch.RischNotImplemented Risch.risch_integrate(sqrt(x + sqrt(x + 1)), x)  # nested
    end

    @testset "$name: radicands that are odd powers (step RP)" begin
        # u = c·w^m, m odd, c = r^m: u^e = (r w)^(e m), then 10a / 10b / 10d with the base r w
        fs = (1 / sqrt(x^3), sqrt(x^3), x * sqrt((x + 1)^3), 1 / sqrt((x^2 + 1)^3), sqrt((x^2 + 1)^3),
              x^2 * (8x^3)^(1 // 3), 1 / sqrt(((x + 2) / (x + 1))^3), sqrt(x^3) + sqrt(x + 1),
              sin(x) / sqrt(cos(x)^3))                      # after the substitution u = cos x (US)
        for f in fs
            F = Risch.risch_integrate(f, x)
            for a in (0.5, 0.9, 1.3)
                @test antiderivative_ok(F, f, a, evalat)
            end
        end
        @test_throws Risch.NotElementary Risch.risch_integrate(sqrt(x^6 + 1), x)      # genus 2 (SI2 phase 1)
    end

    @testset "$name: non-elementary remainders as ₂F₁ terms (phase 6, H1)" begin
        # ∫ xᵐ(α + βxⁿ)^q = α^q x^(m+1)/(m+1) ₂F₁(-q, (m+1)/n; (m+1)/n + 1; -βxⁿ/α) for the residue-free
        # remainder of a binomial radicand (α > 0); the elementary parts stay as they are
        Risch.HYP_ANSWERS[] = true
        try
            val(F, a) = F isa Risch.IntegralWithRootSums ? F(a) : real(evalat(F, complex(a)))
            for (f, pts) in ((1 / sqrt(x^3 + 1), (0.5, 2.0)), (sqrt(x^3 + 1), (0.5, 2.0)),
                             (1 / (x^2 * sqrt(x^3 + 1)), (0.5, 2.0)), (1 / sqrt(1 - x^3), (0.3, -2.0)),
                             (sqrt(x^6 + 1), (0.5, 1.5)), (x / (x^4 + 1)^(1 // 3), (0.5, 2.0)),
                             ((x^2 + 1)^(1 // 3), (0.5, 2.0)),
                             (1 / (x^3 + 1)^(1 // 3) + x^2 / sqrt(x^4 + 1), (0.5, 2.0)))   # log part + ₂F₁
                F = Risch.risch_integrate(f, x)
                @test F isa Risch.IntegralWithRootSums
                for a in pts
                    @test isapprox(fd(t -> val(F, t), a), real(evalat(f, a)); rtol = 1e-6)
                end
            end
            @test occursin("₂F₁(1/2, 1/3; 4/3; -x^3)", string(Risch.risch_integrate(1 / sqrt(x^3 + 1), x)))
            # incomplete gamma (H3): ∫ xˢ e^(bx+d) = -e^d (-b)^(-s-1) Γ(s+1, -bx), b < 0, s ∉ ℤ (half-integers: erf)
            for (f, pts) in ((x^(1 // 3) * exp(-x), (0.5, 2.0)), (exp(-2x) / x^(1 // 3), (0.5, 2.0)),
                             (x^(5 // 4) * exp(1 - x), (0.5, 2.0)), (3x^(1 // 3) * exp(-x) + x^2 * exp(-x), (0.5, 2.0)))
                F = Risch.risch_integrate(f, x)
                for a in pts
                    @test isapprox(fd(t -> val(F, t), a), real(evalat(f, a)); rtol = 1e-6)
                end
            end
            # α < 0 (the argument would cross the branch cut on the domain), or not a binomial: still decided
            @test_throws Risch.NotElementary Risch.risch_integrate(1 / sqrt(x^3 - 1), x)
            @test_throws Risch.NotElementary Risch.risch_integrate(1 / sqrt(x^3 + x + 1), x)
        finally
            Risch.HYP_ANSWERS[] = false
        end
    end

    @testset "$name: denesting square roots (step DN)" begin
        # √(a + b√c) = √((a+d)/2) + sign(b)·√((a-d)/2) when a² - b²c = d² in ℚ(x); valid on the interval of a
        # sample point
        for (f, pts) in ((sqrt(x + sqrt(x^2 - 1)), (1.5, 3.0)), (1 / sqrt(x + sqrt(x^2 - 1)), (1.5, 3.0)),
                         (x / sqrt(x + sqrt(x^2 - 1))^3, (1.5, 3.0)),
                         (sqrt(x + 2sqrt(x - 1)), (2.5, 4.0)), (sqrt(x - 2sqrt(x - 1)), (2.5, 4.0)))
            F = Risch.risch_integrate(f, x)
            for a in pts
                @test antiderivative_ok(F, f, a, evalat)
            end
        end
        # not denestable, a² - b²c = -s²: biquadratic over ℚ(i) (u₁ = y₂ + i s/y₂, u₁² = 2a + 2is), Euler
        # substitution over ℚ(i), exact real parts
        for (f, pts) in ((1 / ((1 + x^4) * sqrt(sqrt(1 + x^4) - x^2)), (0.5, 1.5, -0.7)),     # Rubi
                         (sqrt(sqrt(1 + x^4) + x^2) / (1 + x^4), (0.5, 1.5)))
            F = Risch.risch_integrate(f, x)
            for a in pts
                @test isapprox(fd(t -> real(evalat(F, complex(t))), a), real(evalat(f, a)); rtol = 1e-5)
            end
        end
        # residues outside ℚ(i) in the conjugate piece: not yet
        @test_throws Risch.RischNotImplemented Risch.risch_integrate(sqrt(sqrt(1 + x^4) - x^2), x)
    end

    @testset "$name: radicals of radicands with repeated factors (step SQ)" begin
        # u = s² w, w squarefree: Y = √u/s with Y² = w on every interval (whatever the sign of s); the
        # answers are checked on both sides of the zeros of s
        for (f, pts) in ((1 / sqrt(x^3 - 5x^2 + 3x + 9), (-0.5, 1.0, 2.0, 4.0, 6.0)),   # (x - 3)²(x + 1), Rubi
                         (1 / sqrt(x^3 - 5x^2 + 3x + 9)^3, (-0.5, 1.0, 4.0, 6.0)),
                         (sqrt(x^3 - 5x^2 + 3x + 9), (-0.5, 1.0, 4.0, 6.0)),
                         (x / sqrt((x - 1)^2 * (x^2 + 1)), (-2.0, 0.5, 2.0, 3.0)),    # Euler, w quadratic
                         (sqrt(x^5 + x^4), (-0.5, 1.0, 2.0)),                         # x⁴(x + 1)
                         (sqrt(x^2 + 2x + 1), (-3.0, 1.0)),                           # |x + 1|: w constant
                         (sqrt(2 * (x - 1)^2) / (x + 1), (-0.5, 0.0, 2.0)))
            F = Risch.risch_integrate(f, x)
            for a in pts
                @test antiderivative_ok(F, f, a, evalat)
            end
        end
        for f in (1 / sqrt((x + 2)^2 * (x^3 + 1)), 1 / (x * sqrt(x^2 * (x^3 + 1))))   # w = x³ + 1: genus 1
            @test_throws Risch.NotElementary Risch.risch_integrate(f, x)
        end
        # index n ≥ 3: u = sⁿ (x - a)ʲ (x - b)ᵏ with n | j + k is genus 0, u^(1/n) = s (x - b)^((j+k)/n) v^(j/n),
        # v = (x - a)/(x - b) (step 10a); t is printed through u^(1/n)
        for (f, pts) in ((1 / ((x - 1)^2 * (x + 1))^(1 // 3), (1.5, 3.0, -0.5)),          # Rubi
                         (((x - 1)^2 * (x + 1))^(1 // 3) / x^2, (1.5, 3.0, -0.5)),
                         (1 / (x^3 - 5x^2 + 3x + 9)^(1 // 3), (-0.5, 2.0, 5.0)),
                         (1 / (x^3 - 5x^2 + 3x + 9)^(4 // 3), (-0.5, 2.0, 5.0)),
                         (x * ((x + 2)^3 * (x - 1))^(1 // 4), (1.5, 3.0)),
                         (((x + 1)^2 * (x - 2)^4)^(1 // 3), (2.5, 4.0, 0.5)),
                         ((x^2 - 2x + 1)^(1 // 5) / (1 - x), (0.31, 0.57, 2.0)))   # apostol 21: both sides of 1
            F = Risch.risch_integrate(f, x)
            for a in pts
                @test isapprox(fd(t -> real(evalat(F, complex(t))), a), real(evalat(f, a)); rtol = 1e-5)
            end
        end
    end

    @testset "$name: products of radicals of any index: Hermite reduction (SI2 phase 3a)" begin
        for (f, pts) in (((3x^8 - 2x^5 - x^2 * (3x^3 - 1)^(2 // 3)) / (3x^3 - 1)^(3 // 4), (1.0, 2.0)),   # Rubi
                         (1 / (x^3 + 1)^(4 // 3), (0.5, 2.0)),                     # x/(x³+1)^(1/3)
                         (1 / (x^4 + 1)^(5 // 4), (0.5, 2.0)),
                         (x^2 / (x^3 + 1)^(1 // 3), (0.5, 2.0)),
                         (((x + 1)^(1 // 3) + (x + 2)^(1 // 4)) / ((x + 1)^(1 // 3) * (x + 2)^(1 // 4)), (0.5, 2.0)))
            F = Risch.risch_integrate(f, x)
            for a in pts
                @test isapprox(fd(t -> real(evalat(F, complex(t))), a), real(evalat(f, a)); rtol = 1e-5)
            end
        end
        # Chebyshev: ∫ xᵐ(1 + 2xⁿ)ᵖ is elementary iff (m+1)/n or (m+1)/n + p is an integer (p ∉ ℤ): every
        # case is decided (with the log part of phase 3b)
        val(F, a) = F isa Risch.IntegralWithRootSums ? F(a) : real(evalat(F, complex(a)))
        for n in (3, 4), m in (0, 1, 2), p in (1 // 3, -2 // 3, 1 // 4, -3 // 4)
            f = x^m * (1 + 2x^n)^p
            if isinteger((m + 1) // n) || isinteger((m + 1) // n + p)
                F = Risch.risch_integrate(f, x)
                @test isapprox(fd(t -> val(F, t), 1.7), real(evalat(f, 1.7)); rtol = 1e-5)
            else
                @test_throws Risch.NotElementary Risch.risch_integrate(f, x)
            end
        end
    end

    @testset "$name: the log part for one radical of index q ≥ 3 (SI2 phase 3b)" begin
        # residues r·μ_q with rᵠ in one class tᵠσ; v vanishing at one place of each orbit; the answer is a
        # RootSum over αᵠ = 1 or over zᵠ = σ
        val(F, a) = F isa Risch.IntegralWithRootSums ? F(a) : real(evalat(F, complex(a)))
        for (f, pts) in ((1 / (x^3 + 1)^(1 // 3), (0.5, 2.0)),                          # residues at ∞
                         ((x^3 - 1) / (x^3 + 2)^(1 // 3), (0.5, 2.0)),                  # Rubi
                         (1 / ((x^3 - 1) * (x^3 + 2)^(1 // 3)), (2.0, 3.0)),            # Rubi: finite residues
                         ((3 + 4x^4)^(1 // 4) / x^2, (0.5, 2.0)),                       # Rubi: ℚ(4^(1/4)) = ℚ(√2)
                         (x^2 * (3 + 4x^4)^(5 // 4), (0.5, 2.0)),                       # Rubi
                         (1 / ((x^4 + 1) * (x^4 + 2)^(1 // 4)), (0.5, 2.0)),            # Rubi: class -1, α⁴ + 1
                         ((x^4 + 1)^(3 // 4) / (x^4 + 2)^2, (0.5, 2.0)),                # Rubi
                         (1 / ((x^3 + 3x^2 + 3x) * (x^3 + 3x^2 + 3x + 3)^(1 // 3)), (0.5, 2.0)),   # Rubi
                         (1 / (x * (2x^7 - 27)^(2 // 3)), (2.0, 3.0)),                   # Rubi: ∞ ramified, v = y + 3
                         ((x^7 + 1)^(2 // 3) / x^8, (0.5, 2.0)),                         # Rubi
                         (1 / (x * (x^5 + 1)^(1 // 3)), (0.5, 2.0)))
            F = Risch.risch_integrate(f, x)
            for a in pts
                @test isapprox(fd(t -> val(F, t), a), real(evalat(f, a)); rtol = 1e-5)
            end
        end
    end

    @testset "$name: real forms (log + atan) of the phase-3b log parts" begin
        # Σ_r r log v(r) over r^q = σ (or α^q = 1): real roots give (r/2) log(v²), conjugate pairs
        # μ cos θ log(Re² + Im²) - 2μ sin θ atan(Im/Re); cos, sin in square roots for q = 3, 4, 6 (and 8, 12)
        for (f, pts) in ((1 / (x^3 + 1)^(1 // 3), (0.5, 2.0, -0.5)),
                         (1 / ((x^3 - 1) * (x^3 + 2)^(1 // 3)), (2.0, 3.0)),
                         ((3 + 4x^4)^(1 // 4) / x^2, (0.5, 2.0)),
                         (1 / ((x^4 + 1) * (x^4 + 2)^(1 // 4)), (0.5, 2.0)),          # roots of z⁴ = -1
                         (1 / (x * (x^6 + 1)^(1 // 6)), (0.5, 2.0)),
                         (1 / (x * (x + 1)^(1 // 3) * (x - 1)^(2 // 3)), (2.0, 3.0)))
            F = Risch.risch_integrate(f, x)
            @test !(F isa Risch.IntegralWithRootSums)
            for a in pts
                @test antiderivative_ok(F, f, a, evalat)                       # real-valued at real points
            end
        end
        # q = 5: cos(2π/5) needs nested radicals: the RootSum stays
        @test Risch.risch_integrate(1 / (x * (x^5 + 1)^(1 // 5)), x) isa Risch.IntegralWithRootSums
    end

    @testset "$name: several residue classes, residues of both signs (SI2 phase 3b)" begin
        # classes σᵢ with σᵢ/σⱼ not q-th powers in ℚ(ζ_q) are independent: each class on its own
        val(F, a) = F isa Risch.IntegralWithRootSums ? F(a) : real(evalat(F, complex(a)))
        for (f, pts) in ((1 / ((x^3 - 1) * (x^3 + 2)^(1 // 3)) + (x^3 - 1) / (x^3 + 2)^(1 // 3), (2.0, 3.0)),   # 9 and 1
                         (1 / ((x^3 - 1) * (x^3 + 2)^(1 // 3)) + 1 / (x * (x^3 + 2)^(1 // 3)), (2.0, 3.0)),      # 9 and 4
                         (1 / (x^3 + 1)^(1 // 3) + 1 / (x * (x^3 + 1)^(1 // 3)), (0.5, 2.0)))   # one class, both signs
            F = Risch.risch_integrate(f, x)
            for a in pts
                @test isapprox(fd(t -> val(F, t), a), real(evalat(f, a)); rtol = 1e-5)
            end
        end
        # one class of infinite order is enough
        @test_throws Risch.NotElementary Risch.risch_integrate(1 / (x^3 + 1)^(1 // 3) + 1 / ((x - 2) * (x^3 + 1)^(1 // 3)), x)
        # q = 4 with classes -1 and 8: (-4)^(1/4) ∈ ℚ(i), they may be dependent: no decision
        @test_throws Risch.RischNotImplemented Risch.risch_integrate(1 / ((x^4 + 1) * (x^4 + 2)^(1 // 4)) +
                                                                     1 / (x * (x^4 + 2)^(1 // 4)), x)
    end

    @testset "$name: several radicands in one component (SI2 phase 3b)" begin
        # θ = Π bₖ^rₖ: the integral basis ωⱼ = Π bₖ^{j rₖ} replaces y^k (KumCurve)
        val(F, a) = F isa Risch.IntegralWithRootSums ? F(a) : real(evalat(F, complex(a)))
        for (f, pts) in ((1 / (x * (x + 1)^(1 // 3) * (x - 1)^(2 // 3)), (2.0, 3.0)),     # genus 0
                         (1 / ((x + 1)^(1 // 3) * (x - 1)^(2 // 3)), (2.0, 3.0)),
                         (x / ((x + 2)^(1 // 3) * (x - 1)^(2 // 3) * (x + 3)), (2.0, 3.0)),
                         (1 / ((x + 1)^(1 // 4) * (x - 1)^(3 // 4)), (2.0, 3.0)))
            F = Risch.risch_integrate(f, x)
            for a in pts
                @test isapprox(fd(t -> val(F, t), a), real(evalat(f, a)); rtol = 1e-5)
            end
        end
        for f in (1 / ((x^2 + 1)^(1 // 3) * (x - 1)^(2 // 3)), 1 / (x * (x^2 + 1)^(1 // 3) * (x - 1)^(1 // 3)))
            @test_throws Risch.NotElementary Risch.risch_integrate(f, x)
        end
        # genus 0, search over L off (Nmax = 0): the decision finds order 1 and constructs (q = 3: prime path,
        # q = 4: T_G); the rest reduces exactly
        b0 = Risch.Builder(Risch.auto_build(x, x), Risch.auto_lift(x, x), x)
        Q, QX = Risch.Q, Risch.UPoly{Risch.Q}
        bs = [QX(Q[1, 1]), QX(Q[-1, 1])]
        for (rs, g) in (([Q(1, 3), Q(2, 3)], Risch.frac(QX(Q[1]), QX(Q[0, -1, 0, 1]))),
                        ([Q(1, 4), Q(3, 4)], Risch.frac(QX(Q[1]), QX(Q[-1, 0, 1]))))
            _, _, P, R, D = Risch.kum_component(bs, rs, g, "θ"; needlog = true)
            C = Risch.KumCurve(bs, rs)
            lp = Risch.kum_log_part(C, P, R, D, "θ", b0, "x"; Nmax = 0)
            @test lp isa Tuple
            lp isa Tuple && @test !(Risch.kum_component(bs, rs, Risch.frac(P, C.A) + Risch.frac(R, C.A * D) - lp[1],
                                                         "θ") isa Exception)
        end
    end

    @testset "$name: deciding the log part for an index q ≥ 3 (SI2 phase 3b)" begin
        # q prime: Δ torsion iff its χ-part is iff elementary; the order N₁ of Δ mod one prime, then N₁Δ̄
        # at another prime (different orders: infinite order), or one exact test at N₁ over L
        for f in (1 / ((x - 2) * (x^3 + 1)^(1 // 3)), 1 / ((x - 1) * (x^3 + 2)^(1 // 3)),
                  1 / ((x - 1) * (x^4 + 1)^(1 // 3)), 1 / ((x - 2) * (x^5 + 1)^(1 // 5)))
            @test_throws Risch.NotElementary Risch.risch_integrate(f, x)
        end
        # q composite: T = Π_{ℓ|q}(1 - τ^(q/ℓ)) removes the parts of order < q; orders of T·Δ mod p ≡ 1 mod q
        @test Risch.kum_T(4) == [1, 0, -1, 0] && Risch.kum_T(6) == [1, 0, -1, -1, 0, 1]
        for f in (1 / ((x - 1) * (x^4 + 2)^(1 // 4)), 1 / ((x - 2) * (x^4 + 1)^(1 // 4)),
                  x / ((x - 1) * (x^4 + 3)^(3 // 4)), 1 / ((x - 2) * (x^6 + 1)^(1 // 6)), 1 / ((x - 1) * (x^3 + 2)^(1 // 6)))
            @test_throws Risch.NotElementary Risch.risch_integrate(f, x)
        end
        # consistency: with the search over L switched off (Nmax = 0), torsion cases are still found from
        # the order mod p, never declared non-elementary
        b0 = Risch.Builder(Risch.auto_build(x, x), Risch.auto_lift(x, x), x)
        Q, QX = Risch.Q, Risch.UPoly{Risch.Q}
        for (b, p, q, g) in ((QX(Q[1, 0, 0, 1]), 2, 3, Risch.frac(QX(Q[1]), QX(Q[0, 1, 0, 0, 1]))),
                             (QX(Q[1, 0, 0, 1]), 2, 3, Risch.frac(QX(Q[1]), QX(Q[1, 0, 0, 1]))),
                             (QX(Q[1, 0, 0, 0, 0, 1]), 2, 3, Risch.frac(QX(Q[1]), QX(Q[0, 1, 0, 0, 0, 0, 1]))),
                             (QX(Q[-27, 0, 0, 0, 0, 0, 0, 2]), 1, 3, Risch.frac(QX(Q[1]), QX(Q[0, -27, 0, 0, 0, 0, 0, 0, 2]))))
            c = Risch.kum_component([b], [Q(p, q)], g, "θ"; needlog = true)
            @test c isa Tuple
            _, _, P, R, D = c
            @test Risch.kum_log_part(b, p, q, P, R, D, "θ", b0, "x"; Nmax = 0) isa Tuple
        end
        # composite q, Nmax = 0: the log part is constructed from N·T_G·Δ over L (T_G the Galois trace of T,
        # Θ = χ(T_G) = q here) and what is left reduces exactly (phase 3a)
        @test Risch.kum_TG(6) == [2, 1, -1, -2, -1, 1] && Risch.kum_Theta(Risch.kum_TG(6), 6) == 6
        for (b, p, q, g) in ((QX(Q[1, 0, 0, 0, 1]), 3, 4, Risch.frac(QX(Q[1]), QX(Q[0, 1, 0, 0, 0, 1]))),
                             (QX(Q[1, 0, 0, 0, 1]), 3, 4, Risch.frac(QX(Q[1]), QX(Q[1, 0, 0, 0, 1]))),
                             (QX(Q[1, 0, 0, 0, 0, 0, 1]), 5, 6, Risch.frac(QX(Q[1]), QX(Q[0, 1, 0, 0, 0, 0, 0, 1]))),
                             (QX(Q[3, 0, 0, 0, 4]), 1, 4, Risch.frac(QX(Q[1]), QX(Q[0, 0, 1]))))
            _, _, P, R, D = Risch.kum_component([b], [Q(p, q)], g, "θ"; needlog = true)
            lp = Risch.kum_log_part(b, p, q, P, R, D, "θ", b0, "x"; Nmax = 0)
            @test lp isa Tuple
            lp isa Tuple && @test !(Risch.kum_component([b], [Q(p, q)], Risch.frac(P, b) + Risch.frac(R, b * D) - lp[1],
                                                         "θ") isa Exception)
        end
    end

    @testset "$name: two square roots: the biquadratic splitting (step BQ)" begin
        # f = f₀ + f₁√a + f₂√b + f₃√a√b: each Galois projection on its own (Liouville), √a√b as √(ab)
        ya, yb = sqrt(1 + x^3), sqrt(1 - 2x + x^5)
        for (f, pts) in (((-2ya + 5x^4 * ya - 3x^2 * yb) / (2ya * yb), (0.2, 1.3, 2.0)),   # Rubi: √(x⁵-2x+1) - √(x³+1)
                         (1 / (x * sqrt(x^3 + 1)) + x / sqrt(x^4 + 1), (0.5, 2.0)),
                         (1 / (sqrt(x + 1) * sqrt(x^3 + 1)), (0.5, 2.0)),                  # √(ab) = (x+1)√(x²-x+1)
                         ((sqrt(x^3 + 1) + sqrt(x^3 + 2)) / (x * sqrt(x^3 + 1) * sqrt(x^3 + 2)), (0.5, 2.0)),
                         (x^2 / (sqrt(x^3 + 1) * sqrt(x^3 + 2)), (0.5, 2.0)),             # ab of genus 2: Pell
                         (sqrt(x^3 + x) * sqrt(x^3 + 2x) / x^2, (0.5, 2.0)))              # ab = x²(…): step SQ
            F = Risch.risch_integrate(f, x)
            for a in pts
                @test isapprox(fd(t -> real(evalat(F, complex(t))), a), real(evalat(f, a)); rtol = 1e-5)
            end
        end
        for f in (sqrt(x^3 + 1) * sqrt(x^4 + 1),                        # √(ab), genus 3
                  1 / (sqrt(x^3 + 1) + sqrt(x^3 + 2)))                   # = √(x³+2) - √(x³+1)
            @test_throws Risch.NotElementary Risch.risch_integrate(f, x)
        end
    end

    @testset "$name: Hermite reduction on y² = a, genus ≥ 1 (SI2 phase 1)" begin
        fs = (3x^2 / (2 * sqrt(x^3 + 1)),                       # √(x³+1)
              (x^3 - 2) / sqrt((x^3 + 1)^3),                    # -2x/√(x³+1)
              (x^3 - x) / (2 * x^2 * sqrt(x^3 + x)),            # √(x³+x)/x: a pole at a ramified place
              (5x^4 + 1) / sqrt(x^5 + x + 1)^3 * (x^5 + x + 1) / 2,   # √(x⁵+x+1), genus 2
              x^2 + 1 / (x^2 + 1) + 3x^2 / (2 * sqrt(x^3 + 1)))     # with a rational part
        for f in fs
            F = Risch.risch_integrate(f, x)
            for a in (0.5, 1.3, 2.6)
                @test antiderivative_ok(F, f, a, evalat)
            end
        end
        for f in (1 / sqrt(x^3 + 1),                            # first kind
                  x / sqrt(x^3 + 1),                            # second kind
                  sqrt(x^3 + 1), 1 / sqrt(x^3 + 1)^3, 1 / (x^2 * sqrt(x^3 + 1)),
                  x * sqrt(x^3 + 1)^3, 1 / sqrt(x^4 + 1), x^2 / sqrt(x^4 + 1))
            @test_throws Risch.NotElementary Risch.risch_integrate(f, x)
        end
    end

    @testset "$name: residues at infinity, polynomial Pell equation (SI2 phase 2)" begin
        fs = (x / sqrt(x^4 + 1),                                # log(x² + √(x⁴+1))/2
              x * sqrt(x^4 + 1),                                # with an algebraic part
              (2x + 1) / sqrt(x^4 + 2x^3 + x^2 + 1),            # log(x² + x + √…)
              x^2 / sqrt(x^6 + 1),                              # genus 2
              (6x^5 + 2x) / sqrt((x^6 + x^2)^2 - 4),            # genus 5
              x / sqrt(x^4 + 10x^2 - 96x - 71))                 # Trager: a unit of degree 8
        for f in fs
            F = Risch.risch_integrate(f, x)
            for a in (6.0, 7.5, 9.0)
                @test antiderivative_ok(F, f, a, evalat)
            end
        end
        # genus 1: ∞₊ - ∞₋ of infinite order (Mazur's bound)
        for f in (x^2 / sqrt(x^4 + x^3 + 1), x / sqrt(x^4 + x + 1), (x + 1) / sqrt(x^4 + 1))
            @test_throws Risch.NotElementary Risch.risch_integrate(f, x)
        end
    end

    @testset "$name: rational residues at finite places, torsion divisors (SI2 phase 2)" begin
        y = sqrt(x^4 + x^3 + 3x^2 + 2x + 1)                     # (x² + x + 1)² - x³: v = x² + x + 1 + y, N(v) = x³
        y6 = sqrt(x^6 + 2x^3 - 3x + 1)                          # (x³ + 1)² - 3x, genus 2
        dlv = (2x + 1 + (4x^3 + 3x^2 + 6x + 2) / (2y)) / (x^2 + x + 1 + y)
        fs = (1 / (x * sqrt(x^3 + 1)),                          # log((x³ + 2 - 2√…)/x³)/3, N = 3
              sqrt(x^3 + 1) / x,                                # with an algebraic part
              (3x^3 + 2) / (x * sqrt(x^3 + 1)^3),
              (x^2 + 1) / (x * sqrt(x^4 + 1)),                  # finite and infinite residues
              1 / (x * sqrt(x^4 + 1)),
              1 / (x * sqrt(x^5 + 1)),                          # genus 2, N = 5
              1 / (x * sqrt(x^6 + 1)),
              dlv, dlv - 1 / x,                                 # residues 3/2 at a finite place, -1/2 at ∞₊
              (3x^2 + (6x^5 + 6x^2 - 3) / (2y6)) / (x^3 + 1 + y6))
        for f in fs
            F = Risch.risch_integrate(f, x)
            for a in (2.0, 3.5, 5.0)
                @test antiderivative_ok(F, f, a, evalat)
            end
        end
        # genus 1: the divisor has infinite order (Mazur's bound)
        for f in (1 / (x * sqrt(x^4 + x + 1)), x * dlv + 7 / (x * y),
                  1 / ((x + 1) * sqrt(x^3 + 1)))                # (x + 1) | a: no residues after reduction
            @test_throws Risch.NotElementary Risch.risch_integrate(f, x)
        end
    end

    @testset "$name: quadratic irrational residues ±s√d (SI2 phase 2)" begin
        fs = (1 / (x * sqrt(x^3 + 2)),                          # (√2/6) log(…): residues ±1/√2
              1 / (x * sqrt(x^3 - 2)),                          # imaginary residues: -(√2/6) atan(…)
              1 / (x * sqrt(x^5 - 3)),                          # genus 2, atan
              x / sqrt(2x^4 + 1),                               # ∞ a place of degree 2: (√2/4) log(x² + √(2x⁴+1)/√2)
              1 / (x * sqrt(x^6 + 2)) + x^2 / sqrt(x^6 + 2))    # two classes, √2 and ℚ
        for f in fs
            F = Risch.risch_integrate(f, x)
            for a in (2.0, 3.5, 5.0)
                @test antiderivative_ok(F, f, a, evalat)
            end
        end
        # genus 1, infinite order over ℚ(√d) (Kamienny–Kenku–Momose: N ≤ 18)
        for f in (1 / ((x - 1) * sqrt(x^4 + x + 1)),            # ℚ√3
                  1 / ((x - 1) * sqrt(x^3 + 1)),                # ℚ√2
                  1 / ((x + 2) * sqrt(x^3 + 1)),                # ℚ√-7
                  1 / (x * sqrt(x^3 + 2)) + 1 / ((x + 1) * sqrt(x^3 + 2)),   # the ℚ class fails
                  1 / ((x - 2) * sqrt(x^3 + 1)))                # (2, 3) is torsion, ∫1/√(x³+1) is left
            @test_throws Risch.NotElementary Risch.risch_integrate(f, x)
        end
    end

    @testset "$name: torsion orders mod p; genus 2; residues of degree 4 (SI2 phase 2)" begin
        # genus 2: the orders of the divisor modulo two primes differ
        for f in (x^2 / sqrt(x^6 + x + 1),                      # ∞₊ - ∞₋
                  1 / ((x - 1) * sqrt(x^5 + 1)),                # residues ±1/√2
                  1 / ((x + 1) * sqrt(x^5 + 3)))
            @test_throws Risch.NotElementary Risch.risch_integrate(f, x)
        end
        # residues of degree 4, ℚ-independent: P₁ - σP₁ over a quartic field has infinite order
        for f in (1 / ((x^2 + 1) * sqrt(x^3 + 1)), 1 / ((x^2 - 2) * sqrt(x^3 + 1)))
            @test_throws Risch.NotElementary Risch.risch_integrate(f, x)
        end
        # torsion found mod p, then one exact test
        for f in (1 / (x * sqrt(x^5 + 1)), x / sqrt(x^4 + 10x^2 - 96x - 71))
            F = Risch.risch_integrate(f, x)
            for a in (6.0, 7.5)
                @test antiderivative_ok(F, f, a, evalat)
            end
        end
        # residues of degree > 4: not yet
        @test_throws Risch.RischNotImplemented Risch.risch_integrate(1 / ((x^3 + 2) * sqrt(x^3 + 1)), x)
    end

    @testset "$name: the log part for residues of degree 4: RootSums over a quartic field (SI2 phase 2)" begin
        # P₁ = (1 + √2, (1 + √2)√6) is 4-torsion on y² = 3(x³ - x) (the twist of the 4-torsion point
        # (1 + √2, (1 + √2)√2) of y² = x³ - x), so N(P₁ - σP₁) is principal for N = 2; residues (√2 ∓ 1)/(4√3)
        val(F, a) = F isa Risch.IntegralWithRootSums ? F(a) : real(evalat(F, complex(a)))
        for f in (1 / ((x^2 - 2x - 1) * sqrt(3x^3 - 3x)) + 1 / (4 * sqrt(3x^3 - 3x)),   # L = ℚ(√2, √3)
                  1 / ((x^2 - 2x - 1) * sqrt(x^3 - x)) + 1 / (4 * sqrt(x^3 - x)))      # L = ℚ(√2): r₁ ∈ ℚ(α₁)
            F = Risch.risch_integrate(f, x)          # r₁ = (√6 - √3)/12 is multiquadratic: logs with √3, √6 (classes)
            for a in (1.7, 2.6, 4.1)
                h = 1e-5
                @test isapprox((val(F, a + h) - val(F, a - h)) / (2h), real(evalat(f, a)); rtol = 1e-5)
            end
        end
        # the same log part, but ∫ -dx/(4√(3x³ - 3x)) is left (first kind)
        @test_throws Risch.NotElementary Risch.risch_integrate(1 / ((x^2 - 2x - 1) * sqrt(3x^3 - 3x)), x)
        # the RootSum construction over L = ℚ[z]/(M) (used when the residues are not multiquadratic), called
        # directly on this example: subtracting its derivative leaves exactly -1/4
        Q, QX = Risch.Q, Risch.UPoly{Risch.Q}
        a, Fq, R1 = QX(Q[0, -3, 0, 3]), QX(Q[-1, -2, 1]), QX(Q[1])
        hq = rem(R1 * R1 * Risch.hyp_invmod(Risch.deriv(Fq)^2 * a, Fq), Fq)
        lp = Risch.hyp_quartic_decision(a, R1, Fq, Fq, hq, "u")
        @test lp isa Vector && lp[1][1] === :rootsum && Risch.frac(R1, Fq) - lp[1][5] == Risch.kconst(Q(-1, 4))
    end

    @testset "$name: dependent residues: multiquadratic residues split into classes (SI2 phase 2)" begin
        # r² = A + B√e with A² - eB² a square: r = √p₁ + (B/2p₁)√p₁√e lies in two classes d₁, d₂; residues of
        # different factors in the same class are pooled (one divisor per class)
        y = sqrt(x^3 - x)
        fs = (1 / ((x^2 - 2x - 1) * y) + 1 / (4y),                              # r = (√2 - 1)/4: classes 1, 2
              1 / ((x^2 - 2x - 1) * y) + 1 / ((x^2 + 2x - 1) * y) + 1 / (2y),  # two factors sharing classes 1, 2
              1 / ((x^2 - 2x - 1) * y) + 3 / ((x^2 + 2x - 1) * y) + 1 / y,
              (x + 1) / ((x^2 - 2x - 1) * y) + 1 / (2y),
              # Rubi's library
              x^3 / ((x^4 - 1) * sqrt(2x^8 + 1)),
              (1 - x^2) / ((1 + x^2) * sqrt(1 + x^4)),
              (1 + x^2) / ((1 - x^2) * sqrt(1 + x^2 + x^4)))
        for f in fs
            F = Risch.risch_integrate(f, x)
            for a in (1.7, 2.6, 4.1)
                @test antiderivative_ok(F, f, a, evalat)
            end
        end
        @test_throws Risch.NotElementary Risch.risch_integrate(1 / ((x^2 - 2x - 1) * y) + 1 / ((x^2 + 2x - 1) * y), x)
        f = x / sqrt(1 - x^4)                                                   # residues at ∞ in ℚ√-1: -atan(√(1-x⁴)/x²)/2
        F = Risch.risch_integrate(f, x)
        for a in (-0.7, 0.3, 0.8)
            @test antiderivative_ok(F, f, a, evalat)
        end
    end

    @testset "$name: degree-4 residues mixed with other residues (SI2 phase 2)" begin
        # the residue span is a direct sum (Kummer: square classes of K₁ = ℚ(√d, √e) certified mod p),
        # so each group is decided on its own
        val(F, a) = F isa Risch.IntegralWithRootSums ? F(a) : real(evalat(F, complex(a)))
        y = sqrt(3x^3 - 3x)
        f = 1 / ((x^2 - 2x - 1) * y) + 1 / ((x^2 + 2x - 1) * y) + 1 / (2y)    # two quartic pairs: two RootSums
        F = Risch.risch_integrate(f, x)
        for a in (1.7, 2.6, 4.1)
            h = 1e-5
            @test isapprox((val(F, a + h) - val(F, a - h)) / (2h), real(evalat(f, a)); rtol = 1e-5)
        end
        g4 = 1 / ((x^2 - 2x - 1) * y) + 1 / (4y)                              # elementary on its own
        for f in (g4 + 1 / ((x - 2) * y),                                      # + a class ℚ√2 of infinite order
                  g4 + 1 / ((x - 3) * y),
                  1 / ((x^2 - 2x - 1) * (x^2 + 2x - 1) * y),                   # both pairs torsion, ∫ dx/(8y) left
                  1 / ((x^2 + 1) * (x - 2) * sqrt(x^3 + 1)),                   # quartic pair + rational residues
                  1 / ((x^2 + 1) * (x^2 - 2) * sqrt(x^3 + 1)))                 # two quartic pairs
            @test_throws Risch.NotElementary Risch.risch_integrate(f, x)
        end
    end

    @testset "$name: real log arguments in 10a answers (step RL)" begin
        # t = u^(1/n) > 0: log(-w) where w < 0 on (0, ∞), log(w²)/2 where w changes sign there;
        # SimpleExpressions evaluates in real arithmetic, so a negative log argument would throw
        for (f, pts) in ((1 / sqrt((x + 1) / (x + 2)), (0.5, 2.0, -3.0, -5.0)),
                         (1 / sqrt(((x + 1) / (x + 2))^3), (0.5, 2.0, -3.0)),
                         (sqrt(x) / (x - 1), (0.3, 0.6, 2.0, 5.0)),
                         (1 / (x * sqrt(x + 1)), (0.5, 2.0, -0.5)),
                         (sqrt((x + 2) / (x + 1)), (0.5, 2.0, -3.0)),
                         (1 / (x - x^(1 // 3)), (0.5, 2.0)),
                         (sqrt(x) / (x^2 - 1), (0.4, 3.0)))
            F = Risch.risch_integrate(f, x)
            for a in pts
                @test antiderivative_ok(F, f, a, evalat)
            end
        end
    end

    @testset "$name: real log arguments in Euler substitutions (step EL)" begin
        # real points: ψ(t) = √Q > 0 (10b) or both roots positive (10d); points on every component
        # of the domain, evaluated in real arithmetic by SimpleExpressions
        for (f, pts) in ((1 / (x * sqrt(x^2 + 1)), (0.5, 2.0, -0.5, -2.0)),
                         (sqrt(x^2 + 4x + 3) / (x + 1), (1.0, -4.0)),
                         (1 / (x * sqrt(x^2 + x + 1)), (1.0, -1.0)),
                         (x / sqrt(x^2 - 3x + 2), (3.0, 0.5, -1.0)),
                         (1 / (x * sqrt(x^2 - 1)), (2.0, -2.0)),
                         (1 / (x * sqrt(x + 1) * sqrt(x + 2)), (1.0, 0.5)))
            F = Risch.risch_integrate(f, x)
            for a in pts
                @test antiderivative_ok(F, f, a, evalat)
            end
        end
    end

    @testset "$name: real log arguments over ℚ(√d) (step EC)" begin
        # 10c (constant field ℚ(i)(√d), real form by Step 7) and 10b QuadLogs whose ratio changes
        # sign between the components of the domain; points on both sides, real arithmetic
        for (f, pts) in ((1 / (x * sqrt(2x^2 + 3)), (0.5, 2.0, -0.5, -2.0)),
                         (sqrt(2x^2 + 3) / x, (0.5, -0.5)),
                         (1 / (x * sqrt(3 - 2x^2)), (0.5, -0.5)),
                         (1 / (x * sqrt(3x^2 + x + 2)), (0.4, -1.5, -3.0)))
            F = Risch.risch_integrate(f, x)
            for a in pts
                @test antiderivative_ok(F, f, a, evalat)
            end
        end
    end

    @testset "$name: real log arguments at tower levels (step TL)" begin
        # substitutions with a tower over ℚ(t) (exp(√x), exp(x)): the log arguments in ℚ(t) and
        # the QuadLogs with U, V ∈ ℚ(t) get the signs of EL; points on both sides, real arithmetic
        for (f, pts) in ((exp(sqrt(x)) + sqrt(x) / (x - 1), (0.5, 2.0)),
                         (exp(sqrt(x)) / sqrt(x) + 1 / (x - sqrt(x)), (0.5, 2.0)),
                         (1 / (x * sqrt(x + 1)) + exp(sqrt(x + 1)), (0.5, -0.5)),
                         (1 / (x * sqrt(x^2 + 1)) + exp(x), (0.5, -0.5)),
                         (1 / (x * sqrt(2x^2 + 3)) + exp(x), (0.5, -0.5)),
                         (1 / (x * sqrt(3 - 2x^2)) + exp(x), (0.5, -0.5)))
            F = Risch.risch_integrate(f, x)
            for a in pts
                @test antiderivative_ok(F, f, a, evalat)
            end
        end
    end

    @testset "$name: square roots of quadratics: Euler substitutions (step 10b)" begin
        # (integrand, test points inside the real domain)
        inside = (0.2, 0.45, 0.7)
        right = (1.3, 1.9, 2.6)
        cases = ((1 / sqrt(1 - x^2), inside),           # -2 atan(√(1-x²)/(x+1))  (asin)
                 (sqrt(1 - x^2), inside),
                 (x / sqrt(1 - x^2), inside),
                 (1 / sqrt(3 + 2x - x^2), inside),      # roots -1, 3: t = √Q/(x + 1)
                 (1 / sqrt(1 + x - x^2), inside),       # √C = 1: t = (√Q - 1)/x
                 (1 / sqrt(x^2 + 1), right),            # log(x + √(x²+1))  (asinh)
                 (sqrt(x^2 + 1), right),
                 (1 / sqrt(x^2 - 1), right),            # log(x + √(x²-1))  (acosh)
                 (x / sqrt(x^2 + 2x + 3), right),
                 (1 / (x * sqrt(x^2 + 4)), right),
                 (exp(sqrt(x^2 + 1)) * x / sqrt(x^2 + 1), right))   # e^√(x²+1): an exp level over ℚ(t)
        for (f, pts) in cases
            F = Risch.risch_integrate(f, x)
            for a in pts
                @test antiderivative_ok(F, f, a, evalat)
            end
        end
        @test_throws Risch.NotElementary Risch.risch_integrate((x^2 + 1)^(1//3), x)   # index 3 (phase 3a; Chebyshev)
        @test_throws Risch.NotElementary Risch.risch_integrate(sqrt((x^2 + 1) / (x + 1)), x)   # genus 1 (phase 3a)
    end

    @testset "$name: square roots of quadratics over ℚ(√d) (step 10c)" begin
        inside = (0.2, 0.45, 0.7)
        right = (1.3, 1.9, 2.6)
        cases = ((1 / sqrt(2 - x^2), inside),           # rational point (1, 1): stays over ℚ
                 (sqrt(2 - x^2), inside),
                 (1 / sqrt(3 - x^2), inside),           # point (0, √3) over ℚ(i)(√3): 2 atan((√Q - √3)/x)
                 (sqrt(3 - x^2), inside),
                 (x^2 / sqrt(3 - x^2), inside),
                 (1 / (x * sqrt(3 - x^2)), .-(inside)),   # log((√Q - √3)/x): argument > 0 for x < 0
                 (1 / sqrt(4x - x^2 - 1), right),       # C < 0: the vertex (2, √3)
                 (1 / sqrt(2x^2 + 3), right),           # √A = √2: (√2/2) log(√2 x + √Q)
                 (sqrt(2x^2 + 3), right),
                 (1 / ((x^2 + 1) * sqrt(2x^2 + 3)), right),
                 (1 / (x * sqrt(2x^2 + 3)), right),     # needs √3: second candidate (0, √3)
                 (exp(sqrt(3 - x^2)) * x / sqrt(3 - x^2), inside),
                 (sin(sqrt(2x^2 + 3)) * x / sqrt(2x^2 + 3), right))   # trig over ℚ(i)(√2)
        for (f, pts) in cases
            F = Risch.risch_integrate(f, x)
            for a in pts
                @test antiderivative_ok(F, f, a, evalat)
            end
        end
        @test_throws Risch.NotElementary Risch.risch_integrate(exp(x) * sqrt(3 - x^2), x)
        @test_throws Risch.RischNotImplemented Risch.risch_integrate(1 / sqrt(-x^2 - 1), x)       # never real
        @test_throws Risch.RischNotImplemented Risch.risch_integrate(1 / ((x + 1) * sqrt(3 - x^2)), x)  # √2 and √3
    end

    @testset "$name: two radicands: square roots of linear polynomials (step 10d)" begin
        inside = (0.2, 0.45, 0.7)
        right = (1.3, 1.9, 2.6)
        cases = ((sqrt(x) + sqrt(x + 1), right),        # t = √x + √(x+1): x = ((t - 1/t)/2)²
                 (sqrt(x) * sqrt(x + 1), right),
                 (1 / (sqrt(x) + sqrt(x + 1)), right),
                 (1 / (sqrt(x + 1) - sqrt(x - 1)), right),
                 (sqrt(x) / sqrt(x + 1), right),
                 (1 / (sqrt(x) * sqrt(x + 1)), right),   # 2 log(√x + √(x+1))
                 (x^(3//2) * sqrt(x + 1), right),
                 (sqrt(x) / sqrt(4x + 1), right),
                 (sqrt(2x + 1) * sqrt(3x + 2), right),   # over ℚ(√6)
                 (sqrt(x) * sqrt(1 - x), inside),
                 (log(sqrt(x) + sqrt(x + 1)), right),
                 (exp(sqrt(x) + sqrt(x + 1)) * (1 / sqrt(x) + 1 / sqrt(x + 1)), right))
        for (f, pts) in cases
            F = Risch.risch_integrate(f, x)
            for a in pts
                @test antiderivative_ok(F, f, a, evalat)
            end
        end
        @test_throws Risch.NotElementary Risch.risch_integrate(exp(x) * sqrt(x) * sqrt(x + 1), x)
        @test_throws Risch.RischNotImplemented Risch.risch_integrate(sqrt(x) * sqrt(-x - 1), x)   # never real
        @test_throws Risch.NotElementary Risch.risch_integrate(sqrt(x) * sqrt(x^2 + 1), x)  # genus 1 (step BQ)
        @test_throws Risch.NotElementary Risch.risch_integrate(sqrt(x) * cbrt(x + 1), x)   # phase 3a; Chebyshev
    end

    # SimpleExpressions evaluates sqrt(2) eagerly to a Float64: symbolic constant radicals
    # exist only in SymEngine
    x isa SymEngine.Basic && @testset "$name: square roots of rational constants (step 10e)" begin
        s2, s3 = sqrt(SymEngine.Basic(2)), sqrt(SymEngine.Basic(3))
        right = (1.3, 1.9, 2.6)
        inside = (0.2, 0.45, 0.7)
        cases = ((s2 * x, right),
                 (sqrt(x) * sqrt(2x), right),            # merged by SymEngine into sqrt(2)·x
                 (SymEngine.Basic(2)^(3//2) * x, right), # 2√2 x
                 (1 / (x - s2), right),
                 (sqrt(SymEngine.Basic(8)) / (x + s2), right),
                 (1 / (x^2 + s2 * x + 1), right),        # √2 atan(√2 x + 1)
                 (log(x + s2), right),
                 (exp(s2 * x), right),
                 (x * exp(s2 * x), right),
                 (sin(s2 * x), right),                   # trig over ℚ(i)(√2)
                 (exp(x) / (exp(x) + s2), right),
                 (s2 * sqrt(x), right),                  # with a radical of x (10a)
                 (s2 * sqrt(x) * sqrt(x + 1), right),    # 10d
                 (s2 * sqrt(3 - x^2), inside))           # 10c through the point (1, √2)
        for (f, pts) in cases
            F = Risch.risch_integrate(f, x)
            for a in pts
                @test antiderivative_ok(F, f, a, evalat)
            end
        end
        @test_throws Risch.NotElementary Risch.risch_integrate(s2 * exp(x) * sqrt(3 - x^2), x)
        @test_throws Risch.RischNotImplemented Risch.risch_integrate(s2 * s3 * x, x)              # ℚ(√2, √3)
        @test_throws Risch.RischNotImplemented Risch.risch_integrate(cbrt(SymEngine.Basic(2)) * x, x)
        @test_throws Risch.RischNotImplemented Risch.risch_integrate(sqrt(SymEngine.Basic(6)) * sqrt(3 - x^2), x)
    end

    @testset "$name: parametric Risch DE in towers (step 9d)" begin
        # exact: every basis element (y, c) of y' + f y = Σ cᵢ gᵢ is verified inside `prde`
        Qr = Rational{BigInt}
        hasc(sols, c) = any(s -> s[2] == Qr[c...], sols)
        T0, _ = Risch.build_tower(x^2 + 1, string(x))
        X0 = Risch.frac(Risch.xpoly(Qr))
        k0(c) = Risch.kconst(Qr(c))
        s = Risch.prde(T0, 0, k0(0), Any[k0(1) / X0, k0(1)])       # y' = c₁/x + c₂: c₁ = 0
        @test length(s) == 2 && all(p -> iszero(p[2][1]), s)
        s = Risch.prde(T0, 0, k0(2) / X0, Any[k0(3) * X0])         # weak normalisation; 1/x² homogeneous
        @test length(s) == 2 && hasc(s, (1,)) && hasc(s, (0,))
        T, t = Risch.build_tower(log(x), string(x))
        X = Risch.liftto(T, X0, 1)
        one1 = one(t)
        @test hasc(Risch.prde(T, 1, one1 / X, Any[t]), (1,))       # cancellation: (x y)' = x t
        s = Risch.prde(T, 1, zero(t), Any[one1 / X, t / X])        # ∫ (c₁ + c₂ t)/x in ℚ(x)[t]
        @test length(s) == 3 && hasc(s, (1, 0)) && hasc(s, (0, 2))
        T2, _ = Risch.build_tower(exp(exp(x)), string(x))
        θ1 = Risch.theta(T2, 1)                                     # e^x
        o2 = one(θ1)
        s = Risch.prde(T2, 1, θ1, Any[o2 / (θ1 + o2), o2, θ1 / (θ1 + o2)])
        @test length(s) == 1 && s[1][2] == Qr[1, -1, 1] && iszero(s[1][1])
        @test length(Risch.prde(T2, 1, zero(θ1), Any[θ1, o2 / θ1, Risch.liftto(T2, X0, 1)])) == 4
        # Ei answers above the base level (special_exp through the parametric RDE)
        if ti_special_ok(x)
            fs = (exp(exp(x)) / (exp(x) + 1),          # Ei(eˣ) - e⁻¹ Ei(eˣ + 1): shift from the pole
                  exp(exp(x)) * exp(x) / (exp(x) + 1), # e⁻¹ Ei(eˣ + 1)
                  x * exp(x + exp(x)),                 # x exp(eˣ) - Ei(eˣ): y = x/t
                  exp(x) * log(x),                     # eˣ log x - Ei(x) (in either tower order)
                  exp(2x) * log(x))                    # (e^(2x) log x - Ei(2x))/2
            for f in fs
                F = Risch.risch_integrate(f, x)
                for a in (1.3, 1.9, 2.6)
                    @test antiderivative_ok(F, f, a, evalat)
                end
            end
        else
            @test_skip "SpecialFunctions (expinti) are not defined for $(typeof(x))"
        end
        # no Ei form: still decided
        @test_throws Risch.NotElementary Risch.risch_integrate(x * exp(exp(x)), x)
        @test_throws Risch.NotElementary Risch.risch_integrate(exp(exp(x)) / x, x)
    end

    @testset "$name: decided non-elementary" begin
        # dilogarithm: SimpleExpressions ≥ 1.3.2 has li2 (PolyLog extension); SymEngine has none, so the li2 term
        # is kept as an Expr and evaluated numerically (special-function fallback)
        F = Risch.risch_integrate(log(x) / (x + 1), x)
        @test occursin("li2", string(F))
        name == "SymEngine" && @test F isa Risch.IntegralWithRootSums &&
                                     isapprox((F(2.0 + 1e-6) - F(2.0 - 1e-6)) / 2e-6, log(2.0) / 3; rtol = 1e-5)
        @test_throws Risch.NotElementary Risch.risch_integrate(1 / (x + log(x)), x)
        @test_throws Risch.NotElementary Risch.risch_integrate(x^x, x)
        # tower is [exp(x), log(x)]: top monomial log, normal denominator, non-constant residue
        @test_throws Risch.NotElementary Risch.risch_integrate(exp(x) / (x + log(x)), x)
        # limited integration (step 9d): ∫ lc needs atan / irrational-residue logs, not c·log x
        @test_throws Risch.NotElementary Risch.risch_integrate(log(x) / (x^2 + 2), x)
        @test_throws Risch.NotElementary Risch.risch_integrate(log(x) / (x^2 + 1), x)
        @test_throws Risch.NotElementary Risch.risch_integrate(log(x)^2 / (x^2 - 2), x)
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

    # step TA: atan(u) as a primitive monomial θ' = u'/(1 + u²); non-elementary cases (dilogarithms)
    # are refused, not decided (the structure arguments are for exp/log towers)
    @testset "$name: atan (step TA)" begin
        for f in (atan(x), x * atan(x), atan(x) / (1 + x^2), atan(x)^2 / (1 + x^2), atan(x) / x^2,
                  x^2 * atan(x), atan(2x + 1), exp(atan(x)) / (1 + x^2), atan(log(x)) / x,
                  1 / ((1 + x^2) * atan(x)))
            F = Risch.risch_integrate(f, x)
            for a in (0.4, 1.1, 2.3)
                @test antiderivative_ok(F, f, a, evalat)
            end
        end
        @test_throws Risch.RischNotImplemented Risch.risch_integrate(atan(x) / x, x)
        @test_throws Risch.RischNotImplemented Risch.risch_integrate(atan(x) * log(x), x)
        @test_throws Risch.RischNotImplemented Risch.risch_integrate(atan(1 / x) + atan(x), x)
    end

    # step AS: asin / acos (and integrands whose only radicals are √(K(1 - u²)), √K rational) by the
    # substitution u = sin t / cos t; answers in asin(u), acos(u), u and √(1 - u²), valid for -1 < u < 1
    @testset "$name: asin, acos (step AS)" begin
        for f in (asin(x), acos(x), x * asin(x), asin(x)^2, asin(x) / sqrt(1 - x^2), x * acos(x),
                  asin(x) / x^2, exp(asin(x)) / sqrt(1 - x^2), x^2 * asin(x), sqrt(1 - x^2) * asin(x),
                  1 / sqrt(1 - x^2), sqrt(1 - x^2), x^2 / sqrt(1 - x^2), 1 / sqrt(x - x^2),
                  sqrt(4 - x^2), x / sqrt(9 - 4x^2), asin(2x - 1))
            F = Risch.risch_integrate(f, x)
            for a in (0.15, 0.4, 0.7)
                @test antiderivative_ok(F, f, a, evalat)
            end
        end
        for (f, s) in ((1 / sqrt(1 - x^2), "asin"), (sqrt(1 - x^2), "asin"), (1 / sqrt(x - x^2), "asin"),
                       (acos(x), "acos"))
            @test occursin(s, string(Risch.risch_integrate(f, x)))
        end
        @test_throws Risch.RischNotImplemented Risch.risch_integrate(asin(x) * acos(x), x)   # needs π
    end

    # step AC: acot(u) = atan(1/u); acsc(u) = asin(1/u), asec(u) = acos(1/u) by the reciprocal
    # substitution 1/u = sin t (cos t), answers valid for u > 1; results tidied (rational parts collected)
    @testset "$name: acot, asec, acsc (step AC)" begin
        for (f, pts) in ((acot(x), (0.4, 1.3, -0.7)), (x * acot(x), (0.4, 1.3)), (asec(x), (1.3, 2.2, 4.0)),
                         (acsc(x), (1.3, 2.2, 4.0)), (x * asec(x), (1.3, 2.2)), (asec(x) / x^2, (1.3, 2.2)),
                         (asec(2x + 1), (0.4, 1.3)), (asec(x) / (x * sqrt(x^2 - 1)), (1.3, 2.2)))
            F = Risch.risch_integrate(f, x)
            for a in pts
                @test antiderivative_ok(F, f, a, evalat)
            end
        end
        @test occursin("asec", string(Risch.risch_integrate(x * asec(x), x)))
        @test count("asec", string(Risch.risch_integrate(x * asec(x), x))) == 1      # collected
        @test_throws Risch.RischNotImplemented Risch.risch_integrate(acot(x) + atan(x), x)   # needs π/2
        @test_throws Risch.RischNotImplemented Risch.risch_integrate(asec(x) + acsc(x), x)
    end

    @testset "$name: u-substitution (step US)" begin
        fs = (cos(2x) * sqrt(4 - sin(2x)),                # u = sin 2x
              x^5 / sqrt(1 - x^6),                        # u = x⁶
              x / (sqrt(1 + x^2) * sqrt(1 + sqrt(1 + x^2))),   # u = √(1 + x²)
              sqrt(1 + 3cos(x)^2) * sin(2x),              # u = cos²x
              log(x) / (x * sqrt(1 + log(x))),            # u = log x
              sqrt(1 + sqrt(x)),                          # u = √x (x = u²)
              exp(sqrt(x)) / sqrt(x),
              sin(x) * cos(x)^5 / (1 + cos(x)^6),
              x / (1 + x^4))
        for f in fs
            F = Risch.risch_integrate(f, x)
            for a in (0.5, 0.7, 0.9)
                @test antiderivative_ok(F, f, a, evalat)
            end
        end
        if ti_special_ok(x)                               # Ei(1 + x²)/(2e)
            f = x * exp(x^2) / (1 + x^2)
            F = Risch.risch_integrate(f, x)
            @test all(a -> antiderivative_ok(F, f, a, evalat), (0.5, 0.9))
        end
        @test_throws Risch.NotElementary Risch.risch_integrate(exp(x^2) / (1 + x^2), x)  # no u fits
    end

    @testset "$name: awaiting later stages" begin
        # RootSums over ℚ, ℚ(i), ℚ(e) (steps RT, RC, RE) are tested in test_risch.jl; over ℚ(i)(e)
        # (trigonometric input with e) they are not handled
        @test_throws Risch.RischNotImplemented Risch.risch_integrate(sin(x) + 1 / (x^3 + x + ℯ), x)
    end
end

simple_x = let; SimpleExpressions.@symbolic x; x; end
sym_x = let; SymEngine.@vars x; x; end
run_tests(simple_x, (e, a) -> e isa Function ? e(a) : e, "SimpleExpressions")
run_tests(sym_x, (e, a) -> (z = SymEngine.N(SymEngine.subs(e, sym_x => a));
                            z isa Complex ? ComplexF64(z) : Float64(z)), "SymEngine")

# step SY: symbolic parameters as indeterminates of the constant field (answers for generic values).
# Each package makes its own parameter; derivatives are checked at p = 0.2, x > p.
function sy_tests(x, p, q, r, s1, s2, ev, name)
    @testset "$name: symbolic parameters (step SY)" begin
        sy_fd(F, a) = (ev(F, a + 1e-6) - ev(F, a - 1e-6)) / 2e-6
        for f in (p * x, exp(p * x), x * exp(p * x), 1 / (x + p), 1 / (x^2 - p^2), 1 / (x^2 + p^2), p / (1 + x^2),
                  sin(p * x), x * cos(p * x), log(p * x), x^p, atan(p * x), x / (x^4 + p^2), 1 / (p^2 + exp(2x)))
            F = Risch.risch_integrate(f, x)
            for a in (0.5, 0.75)
                @test isapprox(sy_fd(F, a), ev(f, a); rtol = 1e-5, atol = 1e-8)
            end
        end
        @test occursin("atan", string(Risch.risch_integrate(1 / (x^2 + p^2), x)))   # not a RootSum
        # exp(p) cannot be a constant generator, but as a factor free of x it comes out (step IT)
        let F = Risch.risch_integrate(exp(p) * x, x)
            @test isapprox(sy_fd(F, 0.5), ev(exp(p) * x, 0.5); rtol = 1e-6)
        end
        # three parameters (step PF: Henrici's fraction arithmetic made them practical)
        let f = 1 / (p * x^2 + q * x + r), F = Risch.risch_integrate(f, x)
            @test F isa Risch.IntegralWithRootSums || !isnothing(F)
        end
        # at most MAX_PARAMS = 4 parameters
        @test_throws Risch.RischNotImplemented Risch.risch_integrate(1 / (p * x^4 + q * x^3 + r * x^2 + s1 * x + s2), x)
    end
end
let
    SimpleExpressions.@symbolic x p
    q, r, s1, s2 = let; SimpleExpressions.@symbolic_variables q r s1 s2; (q, r, s1, s2); end   # cap tests
    sy_tests(x, p, q, r, s1, s2, (e, a) -> e isa Function ? e(a, 0.2) : e, "SimpleExpressions")
end
let
    SymEngine.@vars x p q r s1 s2
    sy_tests(x, p, q, r, s1, s2, (e, a) -> real(ComplexF64(SymEngine.N(SymEngine.subs(e, x => a, p => 0.2)))), "SymEngine")
end

# step DL: dilogarithms (PolyLog.li2). The symbolic packages need a method for li2: SimpleExpressions
# (≥ 1.3.2) has it in its PolyLog extension; for SymEngine this stand-in is what a package extension
# would provide (defined here, after the tests above that expect the MethodError of li2(term)).
import PolyLog
const DL_SYMLI2 = SymEngine.SymFunction(:li2)
PolyLog.li2(z::SymEngine.Basic) = DL_SYMLI2(z)
function dl_tests(x, name)
    @testset "$name: dilogarithms (step DL)" begin
        ev(e, a) = real(Risch.term_value(e, "x", a))       # li2 evaluated by PolyLog
        dl_fd(F, a) = (ev(F, a + 1e-6) - ev(F, a - 1e-6)) / 2e-6
        for (f, pts) in ((log(1 + x) / x, (0.3, 1.2, 2.5)), (log(x) / (1 - x), (0.3, 0.7, 2.5)),
                         (log(x) / (1 + x), (0.3, 1.5)), (log(2x + 3) / x, (0.3, 1.5)), (log(x - 2) / x, (2.5, 3.5)),
                         (log(1 + x) / x + x, (0.5, 1.5)), (log(1 + x) / (x * (x - 3)), (0.5, 1.5)))
            F = Risch.risch_integrate(f, x)
            @test occursin("li2", string(F))
            for a in pts
                @test isapprox(dl_fd(F, a), ev(f, a); rtol = 1e-6)
            end
        end
        @test string(Risch.risch_integrate(log(1 + x) / x, x)) in ("-1 * li2(-1 * x)", "-li2(-x)")
        # irrational poles: still decided non-elementary
        @test_throws Risch.NotElementary Risch.risch_integrate(log(1 + x) / (1 + x^2), x)
    end
end
dl_tests(simple_x, "SimpleExpressions")
dl_tests(sym_x, "SymEngine")

# step IT: iterated integrals ∫∫ … dx dy with RootSums (y·RootSum, c(y)·RootSum), definite F(x => b)
let
    SymEngine.@vars x y
    it(f) = Risch.risch_integrate(Risch.risch_integrate(f, x), y)
    @testset "SymEngine: iterated integrals (step IT)" begin
        for (f, fac) in ((1 / (x^3 + x + 1), "y"), (y / (x^3 + x + 1), "y^2"), (exp(y) / (x^3 + x + 1), "exp(y)"),
                         (1 / (x^3 + x + 1) + y^2, "y"))
            F = it(f)
            @test F isa Risch.IntegralWithRootSums && occursin(fac, string(F))
            # ∂²F/∂x∂y = f numerically (central differences)
            val(a, b) = Risch.IntegralWithRootSums(SymEngine.subs(F.elementary, y => b),
                Any[Risch.ScaledRootSum(SymEngine.subs(r.factor, y => b), r.rs) for r in F.rootsums], "x")(a)
            h = 1e-4
            for (a, b) in ((0.5, 0.7), (1.3, 2.0))
                mixed = (val(a + h, b + h) - val(a + h, b - h) - val(a - h, b + h) + val(a - h, b - h)) / (4h^2)
                fv = real(ComplexF64(SymEngine.N(SymEngine.subs(f, x => a, y => b))))
                @test isapprox(mixed, fv; rtol = 1e-5)
            end
        end
        @test_throws Risch.RischNotImplemented it(1 / (x^3 + y))                     # roots depend on y
        G = Risch.risch_integrate(1 / (x^3 + x + 1), x)                               # definite: F(b) - F(a)
        simp(g, a, b; n = 2000) = (hh = (b - a) / n; hh / 3 * (g(a) + g(b) + sum((isodd(k) ? 4 : 2) * g(a + k * hh) for k in 1:(n - 1))))
        @test isapprox(G(x => 2.0) - G(x => 0.0), simp(t -> 1 / (t^3 + t + 1), 0.0, 2.0); atol = 1e-10)
    end
end

# step PR: parameters in a radicand, removed by x = s u + h (Expr terms; checked numerically at sample
# parameter values)
@testset "parameters in radicands (step PR)" begin
    build(op, args...) = Expr(:call, nameof(op), args...)
    ev(e, vals) = Core.eval(Main, Expr(:let, Expr(:block, [Expr(:(=), k, v) for (k, v) in vals]...), e))
    for (f, avals, xs) in ((:((a ^ 2 + -1 * x ^ 2) ^ (5 // 2)), (:a => 2.0,), (0.31, 1.5)),        # apostol 39
                           (:(1 / sqrt(a ^ 2 + -1 * x ^ 2)), (:a => 2.0,), (0.31, 1.5)),           # 87
                           (:(((a + x) / (a + -1x)) ^ (1 // 2)), (:a => 2.0,), (0.31, 1.5)),        # 103
                           (:(sqrt((x + -1a) * (b + -1x))), (:a => 0.2, :b => 0.9), (0.31, 0.57)),  # 104
                           (:(1 / sqrt((x + -1a) * (b + -1x))), (:a => 0.2, :b => 0.9), (0.31, 0.57)),  # 105
                           (:(sqrt((x + -1b) * (a + -1x))), (:a => 0.9, :b => 0.2), (0.31, 0.57)),  # √κ = |σ|
                           (:(x / sqrt(a * x + b)), (:a => 2.0, :b => 1.0), (0.31, 1.5)))
        F = Risch.risch_integrate(f, :x; build = build, lift = identity)
        for x0 in xs
            h = 1e-6
            d = (ev(F, (avals..., :x => complex(x0 + h))) - ev(F, (avals..., :x => complex(x0 - h)))) / (2h)
            @test isapprox(real(d), ev(f, (avals..., :x => x0)); rtol = 1e-5)
        end
    end
end

# asec, acsc: √(1 - 1/u²) is kept (√(u² - 1)/u held for u > 1 only); check both signs
@testset "asec, acsc for u < -1" begin
    build(op, args...) = Expr(:call, nameof(op), args...)
    ev(e, x0) = Core.eval(Main, Expr(:let, :(x = $x0), e))
    for g in (:(asec(x)), :(acsc(x)), :(x * asec(x)), :(asec(2x + 1)))
        F = Risch.risch_integrate(g, :x; build = build, lift = identity)
        for x0 in (-3.5, -2.0, 2.0, 3.0)
            @test isapprox(real((ev(F, complex(x0 + 1e-6)) - ev(F, complex(x0 - 1e-6))) / 2e-6), ev(g, x0); rtol = 1e-5)
        end
    end
end

# Expr terms. Giac.jl writes log as `ln`: the operation name ln is read as log (shown here with
# Expr terms); an Expr has the call 1 // 3 for a rational number; an Expr answer of an inner
# integration (u-substitution) has Symbol operations such as :expinti
@testset "Expr terms" begin
    build(op, args...) = Expr(:call, nameof(op), args...)
    ∫(f, x) = Risch.risch_integrate(f, x; build = build, lift = identity)
    @test ∫(:(x ^ (1 // 3)), :x) isa Expr
    @test ∫(:(1 / (1 + x ^ 2) ^ (3 // 2)), :x) isa Expr
    @test occursin("expinti", string(∫(:((t * exp(t ^ 2)) / (1 + t ^ 2)), :t)))
    for (f, g) in ((:(ln(x)^2), :(log(x)^2)), (:(1 / (x * ln(x))), :(1 / (x * log(x)))), (:(x * ln(x)), :(x * log(x))))
        @test ∫(f, :x) == ∫(g, :x)
    end
end
