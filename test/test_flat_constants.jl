using Test, Random
import RischIntegrate as Risch

# CF{B}, one type for ℚ(t₁, …, tₖ) (flat_constants.jl), against the nested cfield(k, B): random rational functions built
# by the same operations in both, compared through `to_cf`; and gcd, resultant, squarefree parts of polynomials in x
# over the field, compared coefficient by coefficient
@testset "CF: one type for the constant field, against the nested types" begin
    Q = Risch.Q
    for B in (Q, Risch.QI), k in 1:4
        C = Risch.cfield(k, B)
        F = Risch.CF{B}
        rng = MersenneTwister(17k + (B === Q ? 0 : 100))
        gens = [(Risch.tgen(C, j), Risch.cf_gen(F, j)) for j in 1:k]
        small() = (q = Q(rand(rng, -5:5), rand(rng, 1:4)); (Risch.cfromQ(C, q), Risch.cfromQ(F, q)))
        function rnd(depth)
            depth == 0 && return rand(rng) < 0.6 ? gens[rand(rng, 1:k)] : small()
            (a, a′), (b, b′) = rnd(depth - 1), rnd(depth - 1)
            r = rand(rng, 1:4)
            r == 1 && return (a + b, a′ + b′)
            r == 2 && return (a - b, a′ - b′)
            r == 3 && return (a * b, a′ * b′)
            iszero(b) ? (a * b, a′ * b′) : (a / b, a′ / b′)
        end
        for _ in 1:40
            c, c′ = rnd(3)
            @test Risch.to_cf(F, c) == c′
            @test Risch.from_cf(C, c′) == c
            @test hash(Risch.to_cf(F, c)) == hash(c′)
            iszero(c) || @test isone(c′ * inv(c′))
            @test iszero(c′ - c′)
        end
        # polynomials in x over the field: gcd, resultant, squarefree factorization (coefficients generators or small
        # rationals: random nested fractions as coefficients take minutes in either representation)
        P, P′ = Risch.UPoly{C}, Risch.UPoly{F}
        rpoly(d) = (cs = [rnd(0) for _ in 0:d]; (P([c for (c, _) in cs]), P′([c′ for (_, c′) in cs])))
        conv(p) = P′([Risch.to_cf(F, c) for c in p.c])
        for _ in 1:6
            (g, g′), (a, a′), (b, b′) = rpoly(1), rpoly(2), rpoly(2)
            A, A′, Bp, B′ = g * a, g′ * a′, g * b, g′ * b′
            @test conv(gcd(A, Bp)) == gcd(A′, B′)
            @test Risch.to_cf(F, Risch.resultant(a, b)) == Risch.resultant(a′, b′)
            sq, sq′ = Risch.squarefree(A * g), Risch.squarefree(A′ * g′)
            @test [conv(p) => m for (p, m) in sq] == sq′
            @test Risch.csize(A) == Risch.csize(A′)   # (step RB's size test)
        end
        # zero coefficients count 0 above depth 0, as in the nested types: x⁴ + t₁ has 3 rational coefficients (t₁ = 0 + 1·t₁),
        # not 6
        @test Risch.csize(P′([gens[1][2], zero(F), zero(F), zero(F), one(F)])) ==
              Risch.csize(P([gens[1][1], zero(C), zero(C), zero(C), one(C)])) == 3
    end
end

# sample 393, refused under CF by step RB's size test (csize counted the CF's zeros), and sample 1327, refused after
# #148 (step LS no longer split d⁻¹ (e cos y)^(5/2) (a + a sin y) after step AL's y = c + d x)
@testset "CF: csize; step LS over a constant denominator" begin
    build(op, args...) = Expr(:call, op isa Symbol ? op : nameof(op), args...)
    hyp = Risch.HYP_ANSWERS[]
    Risch.HYP_ANSWERS[] = true   # (the default; test_integrate.jl turns it off)
    for f in (:((c + d * x ^ 2) ^ 3 / (x ^ (9 / 2) * (a + b * x ^ 2))), :((e * cos(c + d * x)) ^ (5 / 2) * (a + a * sin(c + d * x))))
        @test Risch.risch_integrate(f, :x; build = build, lift = identity) isa Expr
    end
    Risch.HYP_ANSWERS[] = hyp
end

# CF methods for helpers written on a bare ::Frac (lead_rational: a MethodError on ∫ (1 - cos(π y z))/(y z) dy, SymJ's
# second integration of ∫∫∫ sin(xyz), SymPy #5741, with CF the default)
@testset "CF: lead_rational, pos_even" begin
    C = Risch.CF{Risch.QI}
    t1 = Risch.cf_gen(C, 1)
    @test Risch.lead_rational(Risch.cfromQ(C, Risch.Q(-3, 2))) == -3 // 2
    @test Risch.lead_rational(-2 * t1 + Risch.cfromQ(C, Risch.Q(5))) == -2
    @test Risch.pos_even(Risch.cfromQ(Risch.CF{Risch.Q}, Risch.Q(3)))
    build(op, args...) = Expr(:call, op isa Symbol ? op : nameof(op), args...)
    import SpecialFunctions
    ev(e, y0) = Core.eval(Main, Expr(:let, Expr(:block, :(y = $y0), :(z = 0.7), :(cosint = $(SpecialFunctions.cosint))), e))
    for f in (:((1 - cos(pi * y * z)) / (y * z)), :((1 - cos(y * z)) / (y * z)))
        F = Risch.risch_integrate(f, :y; build = build, lift = identity)
        @test occursin("cosint", string(F))
        for y0 in (0.4, 1.7, 3.1)
            @test isapprox((ev(F, y0 + 1e-6) - ev(F, y0 - 1e-6)) / 2e-6, ev(f, y0); rtol = 1e-6)
        end
    end
end
