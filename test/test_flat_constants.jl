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
        end
    end
end
