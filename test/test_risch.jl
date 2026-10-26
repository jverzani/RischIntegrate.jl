using Test
import SymEngine
using RischIntegrate
import RischIntegrate as Risch

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
    res = Risch.integrate_rational(rf(poly(1), poly(1, 1, 0, 1)))      # 1/(x^3+x+1)
    @test !isempty(res.unresolved)
    # an even quartic: nested real forms (step BQ4), exact derivative
    f = rf(poly(1), poly(2, 0, 0, 0, 1))                                # 1/(x^4+2)
    res = Risch.integrate_rational(f)
    @test isempty(res.unresolved) && Risch.derivative_of(res) == f
end

# step WR: Hermite reduction with a repeated factor V of degree ≥ 2 next to other factors (the new
# numerator is C + U B'/j, U = D/V^(j+1)); before the fix these failed the self-check
@testset "Hermite reduction: repeated factor of degree ≥ 2 with other factors" begin
    for f in (rf(poly(1), poly(1, 0, 1) * poly(2, 0, 1)^2),                 # 1/((x²+1)(x²+2)²)
              rf(poly(1), poly(-1, 1) * poly(1, 0, 1)^2),                   # 1/((x-1)(x²+1)²)
              rf(poly(0, 0, -9//2), poly(1//4, 0, -3//4, 0, 0, 0, 1)),      # (x²+1)(x²-1/2)²
              rf(poly(1, 0, 0, 1), poly(-1, 1) * poly(1, 1, 1)^3))          # (x-1)(x²+x+1)³
        g, Qp, R, D = Risch.hermite_reduce(Risch.dx, f.num, f.den)
        @test Risch.dx(g) + rf(Qp, poly(1)) + rf(R, D) == f
        res = Risch.integrate_rational(f)
        @test isempty(res.unresolved) && Risch.derivative_of(res) == f
    end
end

# step WR: a leaf that prints with the variable in it (a wrapper type such as Symbolics' Num, for
# which `iscall` is false) is refused, not taken as a parameter (∫ f dx = f·x); numeric leaves
# printed as (p//q) are numbers
struct WrLeaf
    s::String
end
Base.show(io::IO, w::WrLeaf) = print(io, w.s)
@testset "opaque leaves and rational leaves (step WR)" begin
    xs = let; SymEngine.@vars x; x; end
    @test_throws Risch.RischNotImplemented Risch.risch_integrate(WrLeaf("1 / (1 + x)"), xs)
    @test_throws Risch.RischNotImplemented Risch.risch_integrate(WrLeaf("exp(x)*x"), xs)
    @test !Risch.mentions_var("x1 + max(y, 2)", "x")
    @test Risch.mentions_var("sin(x)^2", "x")
    @test Risch.leaf_rational(WrLeaf("(1//3)")) == Q(1, 3)
    @test Risch.leaf_rational(WrLeaf("-2//5")) == Q(-2, 5)
    @test Risch.leaf_rational(WrLeaf("(a)")) === nothing
end

@testset "RootSum: residues of degree > 2, verified in the exact field" begin
    for f in (rf(poly(1), poly(1, 1, 0, 1)),                          # 1/(x³+x+1)
              rf(poly(0, 1), poly(1, 1, 0, 1)^2),                     # x/(x³+x+1)²  (Hermite part too)
              rf(poly(1), poly(-2, 0, 0, 1) * poly(-3, 0, 0, 1)),     # 1/((x³-2)(x³-3))
              rf(poly(1), poly(1, 1, 0, 0, 0, 1)))                    # 1/(x⁵+x+1)
        res = Risch.integrate_rational(f)
        @test !isempty(res.unresolved)
        rss = vcat([Risch.root_sums(rest, R, D, "x") for (rest, R, D) in res.unresolved]...)
        el = Risch.RationalIntegral(res.rational, res.logs, res.atans, Any[], res.quads)
        @test Risch.derivative_of(el) + sum(Risch.rootsum_derivative(rs) for rs in rss) == f
    end
    # even quartic factors (needing 2^(1/4)): nested real forms instead (step BQ4), exact derivative
    for f in (rf(poly(1), poly(2, 0, 0, 0, 1)), rf(poly(1), poly(3, 0, 1) * poly(2, 0, 0, 0, 1)))   # 1/(x⁴+2), 1/((x²+3)(x⁴+2))
        res = Risch.integrate_rational(f)
        @test isempty(res.unresolved) && Risch.derivative_of(res) == f
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
    # Lazard–Rioboo–Trager (step LR): W from subresultants, also for a residue shared by two roots
    # (x/(x⁶+x²+1): residues 1/(2(3y²+1)) at y³+y+1 = 0, y = x², so deg W = 2)
    for (A, D, degW) in ((poly(1), poly(1, 1, 0, 1), 1), (poly(1), poly(1, 1, 0, 0, 1), 1),
                         (poly(0, 1), poly(1, 0, 1, 0, 0, 0, 1), 2))
        f = rf(A, D)
        res = Risch.integrate_rational(f)
        rest, R, Dd = res.unresolved[1]
        lr = Risch.lrt_logs(Risch.monic(rest), Dd, R, Risch.deriv(Dd))
        @test lr !== nothing && all(p -> length(p[2]) == degW + 1, lr)
        rss = Risch.root_sums(rest, R, Dd, "x")
        el = Risch.RationalIntegral(res.rational, res.logs, res.atans, Any[], res.quads)
        @test Risch.derivative_of(el) + sum(Risch.rootsum_derivative(rs) for rs in rss) == f
    end
    # step SD: the factor free of the generator e splits the residue computation
    let C = Risch.Frac{Risch.UPoly{Q}}, e = Risch.tgen(C, 1), c = q -> Risch.cfromQ(C, Q(q))
        P = Risch.UPoly{C}
        D = P([c(1), c(0), c(1)]) * P([e, c(1), c(0), c(0), c(1)])
        @test Risch.tfree_factor(D) == P([c(1), c(0), c(1)])
        @test Risch.tfree_factor(P([e, c(1), c(0), c(0), c(1)])) === nothing
        res = Risch.integrate_rational(Risch.frac(P([c(1)]), D))
        @test sort([Risch.degree(u[1]) for u in res.unresolved]) == [4]   # the 1+s² part: real form (SY)
        @test !isempty(res.atans)
    end
    # Bareiss determinant
    @test Risch.field_det(Q[2 1 3; 0 4 1; 5 2 0]) == Q(-59)
    @test Risch.field_det(Q[0 1; 1 0]) == Q(-1)
    # quadratic residue factors are split off over ℚ: only the quartic is left for RootSum
    res = Risch.integrate_rational(rf(poly(1), poly(3, 0, 1) * poly(1, 1, 0, 0, 1)))
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
    # roots not in ℚ(i, √d): for an even quartic, nested real forms (step BQ4); otherwise a RootSum
    for f in (rf(poly(1), poly(2, 0, 0, 0, 1)), rf(poly(1), poly(3, 0, 1, 0, 1)))       # 1/(x⁴+2), 1/(x⁴+x²+3)
        res = Risch.integrate_rational(f)
        @test isempty(res.unresolved) && any(q -> q isa Risch.BiquadTerm, res.quads) && Risch.check_result(res, f)
    end
    @test !isempty(Risch.integrate_rational(rf(poly(1), poly(1, 1, 0, 0, 1))).unresolved)   # 1/(x⁴+x+1)
    # step NR: nested radicals √w, w ∈ ℚ(√d) (Im ζ₁₀ = √(10 − 2√5)/4): 1/(x⁵+1) etc. in real form
    for N in (poly(1), poly(0, 1), poly(0, 0, 0, 1))
        f = rf(N, poly(1, 0, 0, 0, 0, 1))
        res = Risch.integrate_rational(f)
        @test isempty(res.unresolved)
        @test any(q -> q isa Risch.QuarticNested, res.quads)
        @test Risch.check_result(res, f)
    end
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
        # a binomial denominator: x = 2^(1/4) u (or ℯ^(1/4) u), then a quartic over ℚ (step BN); an even quartic
        # with nested real forms (step BQ4)
        for f in (1/(x^4 + 2), 1/(x^4 + ℯ), 1/((x^2 + 3)*(x^4 + 2)), 1/((x^2 + 1)*sqrt(x + 1)))   # t⁴ - 2t² + 2
            F = Risch.risch_integrate(f, x)
            @test !(F isa Risch.IntegralWithRootSums)
            for a in (1.7, 2.6, 4.1)
                @test isapprox(fd(t -> evalat(F, t), a), evalat(f, a); rtol = 1e-5)
            end
        end
        # residues algebraic of degree > 2: elementary part + RootSums (verified exactly
        # inside), evaluated numerically by F(a)
        for f in (1/(x^3 + x + 1), x/(x^3 + x + 1), 1/(x^3 + x + 1)^2,
                  1/(x^5 + x + 1), (x^2 + 1)/(x^6 + x + 1), 1/((x^2 + 3)*(x^4 + x + 1)))
            F = Risch.risch_integrate(f, x)
            @test F isa Risch.IntegralWithRootSums
            @test occursin("RootSum", string(F))
            for a in (0.3, 1.7, 2.6)
                @test isapprox(fd(F, a), evalat(f, a); rtol = 1e-5)
            end
        end
        # a RootSum in a substitution variable (t = sqrt(1 + x), Euler's t) is evaluated through x
        for f in (1/((x^3 + 2)*sqrt(x + 1)), 1/((x^3 + x + 1)*sqrt(x^2 + 1)))
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
        # nested-radical real forms (step NR): no RootSum, continuous, F(b) - F(a) by Simpson
        nr_simpson(g, a, b; n = 1000) = (h = (b - a) / n;
            h / 3 * (g(a) + g(b) + sum((isodd(k) ? 4 : 2) * g(a + k * h) for k in 1:(n - 1))))
        for f in (1/(x^5 + 1), x/(x^5 + 1), x^3/(x^5 + 1))
            F = Risch.risch_integrate(f, x)
            @test !(F isa Risch.IntegralWithRootSums) && occursin("sqrt(", string(F))
            @test maximum(abs.(diff([evalat(F, a) for a in 0:0.05:4]))) < 0.1
            @test isapprox(evalat(F, 4.0) - evalat(F, 0.0), nr_simpson(t -> evalat(f, t), 0.0, 4.0); atol = 1e-8)
        end
        # RootSums over ℚ(i) in trigonometric towers (step RC): complex coefficients R + i·I in cos/sin;
        # F(a) is the real part (an antiderivative between the branch-cut jumps of the complex logs)
        for f in (cos(x)/(sin(x)^3 + sin(x) + 1), 1/(cos(x)^3 + 2), cos(x)/(sin(x)^4 + sin(x) + 2),
                  sin(x) + 1/(x^3 + x + 1), 1/(sin(x)^3 + 2))
            F = Risch.risch_integrate(f, x)
            @test F isa Risch.IntegralWithRootSums
            @test occursin("RootSum", string(F))
            for a in (0.3, 1.1, 2.3)
                @test isapprox(fd(F, a), evalat(f, a); rtol = 1e-5)
            end
        end
        # continuous evaluation (step RN): F(a) continues the logs of a RootSum from a reference
        # point, so F is continuous and F(b) - F(a) is the definite integral (Simpson's rule)
        simpson(g, a, b; n = 1000) = (h = (b - a) / n;
            h / 3 * (g(a) + g(b) + sum((isodd(k) ? 4 : 2) * g(a + k * h) for k in 1:(n - 1))))
        for (f, a, b) in ((1/(cos(x)^3 + 2), 0.0, 13.0), (sin(x)/(cos(x)^4 + cos(x) + 2), -3.0, 6.0),
                          (cos(x)/(sin(x)^3 + sin(x) + 3), 0.0, 7.0), (1/(x^3 + x + 1), 0.0, 5.0),
                          (1/(exp(3x) + exp(x) + 1), -3.0, 3.0))
            F = Risch.risch_integrate(f, x)
            @test maximum(abs.(diff([F(c) for c in a:0.05:b]))) < 0.1
            @test isapprox(F(b) - F(a), simpson(t -> evalat(f, t), a, b); atol = 1e-8)
        end
        # RootSums over a transcendental constant field ℚ(e) (step RE): polynomial coefficients are
        # terms (exp(1)), base level, log/exp levels and base-level RootSums inside a tower
        re_simpson(g, a, b; n = 1000) = (h = (b - a) / n;
            h / 3 * (g(a) + g(b) + sum((isodd(k) ? 4 : 2) * g(a + k * h) for k in 1:(n - 1))))
        for f in (1/(x^3 + x + ℯ), 1/(x*(log(x)^3 + log(x) + ℯ)), exp(x)/(exp(3x) + ℯ*exp(x) + 1),
                  exp(x) + 1/(x^3 + ℯ), 1/((x^2 + 1)*(x^4 + x + ℯ)),
                  # step ST: the e-free factor split off at a log / an exp level
                  1/(x*(log(x)^2 + 1)*(log(x)^4 + log(x) + ℯ)), exp(x)/((exp(2x) + 1)*(exp(4x) + exp(x) + ℯ)))
            F = Risch.risch_integrate(f, x)
            @test F isa Risch.IntegralWithRootSums
            @test all(rs -> rs isa Risch.TermRootSum, F.rootsums)
            for a in (1.3, 2.1, 2.9)
                @test isapprox(fd(F, a), evalat(f, a); rtol = 1e-5, atol = 1e-9)
            end
            @test isapprox(F(3.0) - F(1.1), re_simpson(t -> evalat(f, t), 1.1, 3.0); atol = 1e-8)
        end
        # nested-radical real forms at tower levels (step NT): log, exp and log(log) levels
        nt_simpson(g, a, b; n = 1000) = (h = (b - a) / n;
            h / 3 * (g(a) + g(b) + sum((isodd(k) ? 4 : 2) * g(a + k * h) for k in 1:(n - 1))))
        for (f, a, b) in ((1/(x*(log(x)^5 + 1)), 1.1, 6.0), (exp(x)/(exp(5x) + 1), -2.0, 2.0),
                          (log(x)/(x*(log(x)^5 + 1)), 1.1, 6.0))
            F = Risch.risch_integrate(f, x)
            @test !(F isa Risch.IntegralWithRootSums) && occursin("sqrt(", string(F))
            @test maximum(abs.(diff([evalat(F, t) for t in a:0.05:b]))) < 0.1
            @test isapprox(evalat(F, b) - evalat(F, a), nt_simpson(t -> evalat(f, t), a, b); atol = 1e-8)
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

sym_x = let; SymEngine.@vars x; x; end
# SymEngine may evaluate a real answer (atan, log with sqrt(2) inside) with a roundoff-size
# imaginary part; drop only that (as `trig_sym_eval` in test_trig.jl)
function risch_sym_eval(e, a)
    z = SymEngine.N(SymEngine.subs(e, sym_x => a))
    z isa Complex || return Float64(z)
    w = ComplexF64(z)
    abs(imag(w)) <= 1e-10 * max(1.0, abs(w)) ? real(w) : w
end
run_tests(sym_x, risch_sym_eval, "SymEngine")
