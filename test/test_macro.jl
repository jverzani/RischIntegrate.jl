using Test
import RischIntegrate as Risch
import RischIntegrate: @integrate

# @integrate: integrate for Julia expressions, without quoting (as GruntzLimit's @limit)
@testset "@integrate" begin
    ev(e, x0) = Core.eval(Main, Expr(:let, :(x = $x0), e))
    F = @integrate(x * exp(x), x)
    @test F isa Expr
    for a in (0.3, 1.7)
        @test isapprox((ev(F, a + 1e-6) - ev(F, a - 1e-6)) / 2e-6, a * exp(a); rtol = 1e-6)
    end
    @test @integrate(sin(x), (x, 0, π)) ≈ 2
    @test @integrate(x ^ 2, (x, 1, 2)) ≈ 7 / 3
    @test @integrate(1 / (x ^ 3 + 2), (x, 0, 1)) ≈ 0.450822129263755          # (a RootSum)
    @test @integrate(x ^ 2 * y, (x, 0, 1), (y, 0, 2)) ≈ 2 / 3                   # iterated, definite
    G = @integrate(x ^ 2 * y, x, y)                                              # iterated
    @test Core.eval(Main, Expr(:let, Expr(:block, :(x = 2.0), :(y = 3.0)), G)) ≈ 8 / 3 * 9 / 2
    n = 3
    @test string(@integrate(x ^ $n, x)) == string(@integrate(x ^ 3, x))          # $n: the value of n
    H = @integrate(a * x ^ 2, (x, 0, 1))                                         # a parameter: an Expr
    @test H isa Expr && Core.eval(Main, Expr(:let, :(a = 3), H)) ≈ 1
    @test @integrate(sin(x), (x, 0, :b)) isa Expr                                # a symbolic bound
    @test string(@integrate(x * exp(x), x, verify = false)) == string(F)         # keywords passed on
    @test_throws Risch.NotElementary @integrate(x ^ x, x)
    @test_throws ArgumentError macroexpand(@__MODULE__, :(@integrate(sin(x), 3)))
    @test_throws ArgumentError macroexpand(@__MODULE__, :(@integrate(sin(x))))
end
