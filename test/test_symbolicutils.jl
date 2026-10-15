using Test
using SymbolicUtils
using SymbolicUtils: @syms
using RischIntegrate
import RischIntegrate as Risch

# step SB: SymbolicUtils terms are integrated directly (TermInterface); constants such as sqrt(2)
# are built with `maketerm` and stay exact, li2 of a term is built the same way

@syms x::Real y::Real

su_value(e, a) = SymbolicUtils.unwrap_const(SymbolicUtils.substitute(e, Dict(x => a); fold = Val(true)))
function su_ok(F, f, a; h = 1e-6)
    dF = (su_value(F, a + h) - su_value(F, a - h)) / (2h)
    fv = su_value(f, a)
    dF isa Number && fv isa Number && abs(dF - fv) <= 1e-6 * max(1, abs(fv))   # li2 returns a Complex
end

@testset "SymbolicUtils terms (step SB)" begin
    for (f, has) in ((1 / (x^2 + 2), "sqrt(2)"),
                     (1 / (x^4 + 1), "sqrt(2)"),
                     (1 / (2x^2 + 3), "sqrt(6)"),
                     (exp(-x^2), "sqrt(π)"),
                     (sqrt(x) / (x - 1), "log"),
                     (x * exp(x), "exp"),
                     (log(x) / (1 + x), "li2"),
                     (atan(x), "atan"))
        F = integrate(f, x)
        s = string(F)
        @test occursin(has, s)
        @test !occursin(r"\d\.\d{4}", s)                 # no floating point constants
        for a in (0.4, 2.5)
            @test su_ok(F, f, a)
        end
    end
    @test string(integrate(x * y, x, y)) == "(1//4)*(x^2)*(y^2)"
    @test integrate(1 / (x^3 + 2), x) isa Risch.IntegralWithRootSums
end
