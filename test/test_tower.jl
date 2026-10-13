using Test
import SimpleExpressions
import SymEngine
include("Risch.jl")
using .Risch

fd(f, a; h = 1e-6) = (f(a + h) - f(a - h)) / (2h)

# number of generators of the (minimal) tower for f, and their kinds
function shape(f, x)
    T, el = Risch.build_tower(f, string(x))
    [lv.kind for lv in T.levels]
end
# the transcendental constants (generators of the constant field) the tower needed
consts(f, x) = Set(Risch.build_tower(f, string(x))[1].consts)
G(kind, a) = Risch.ConstGen(kind, Rational{BigInt}(a))

function run_tests(x, evalat, name)
    @testset "$name: tower structure" begin
        @test shape(1/(x^2 + 1), x) == Symbol[]
        @test shape(exp(x), x) == [:exp]
        @test shape(exp(2x) + exp(x), x) == [:exp]              # exp(2x) = θ²
        @test shape(exp(x/2) + exp(x), x) == [:exp]
        @test shape(exp(x) + exp(x/2) + exp(x/3), x) == [:exp]  # restart: θ = exp(x/6)
        @test shape(exp(-x) / (1 + exp(x)), x) == [:exp]
        # SymEngine merges exp(x)*exp(x^2) into exp(x + x^2) before we see it (1 generator);
        # SimpleExpressions keeps the product (2 generators). Both towers are valid.
        @test length(shape(exp(x) * exp(x^2), x)) in (1, 2)
        @test shape(exp(x + x^2) + exp(x) + exp(x^2), x) == [:exp, :exp]   # dependent: 2 not 3
        @test shape(exp(x) / exp(x) + x, x) == Symbol[]
        @test shape(exp(log(x)), x) == Symbol[]                 # = x
        @test shape(log(exp(x)), x) == Symbol[]                 # = x
        @test shape(exp(2 * log(x)), x) == Symbol[]             # = x^2
        @test shape(log(x) + log(x^2) + log(x + 1) + log(x^2 + x), x) == [:log, :log]
        @test shape(log(x^2 - 1) + log(x - 1), x) == [:log, :log]
        # log(x+1) = log(x^2-1) - log(x-1): the sum is 2 log(x^2-1). Whether that needs one
        # generator or two depends on the order the package stores the sum's terms
        # (SymEngine's sums are unordered), so only the bound is a property of the input.
        @test length(shape(log(x^2 - 1) + log(x - 1) + log(x + 1), x)) in (1, 2)
        @test shape(log(x^2 - 1) - log(x - 1) - log(x + 1), x) == Symbol[]   # identically 0
        @test shape(x^x, x) == [:log, :exp]
        @test shape(sinh(x) + cosh(x) + exp(x), x) == [:exp]
        @test shape(exp(exp(x)), x) == [:exp, :exp]
        @test shape(log(log(x)), x) == [:log, :log]
    end

    @testset "$name: tower derivation agrees with the ordinary derivative" begin
        fs = (exp(x), exp(2x) + exp(x), exp(x/2) + exp(x), x * exp(x^2), log(x)/x,
              log(x^2 - 1), log(x) * log(x + 1), x^x, exp(exp(x)), log(log(x)),
              sinh(x) * cosh(x), tanh(x), exp(-x) / (1 + exp(x)),
              exp(x + log(x)), exp(x + x^2) / (1 + exp(x)),  1/(x*log(x)), x^2 * exp(-x),
              exp(x) + exp(x + 1), x * exp(x + 1) + exp(x), log(x) * log(2x), 2^x, x * 3^x,
              log(x) + log(6x), exp(x) * exp(x + 1//2))
        for f in fs
            d = Risch.tower_derivative(f, x)
            for a in (1.7, 2.6, 4.1)
                @test isapprox(evalat(d, a), fd(t -> evalat(f, t), a); rtol = 1e-5, atol = 1e-8)
            end
        end
    end

    @testset "$name: transcendental constants (Step 6)" begin
        # alone, exp(x+1) and log(2x) are simply their own generators (no constants)
        @test shape(exp(x + 1), x) == [:exp] && isempty(consts(exp(x + 1), x))
        @test shape(log(2x), x) == [:log] && isempty(consts(log(2x), x))
        # together with exp(x) / log(x) the constants e, log 2 appear; the order the package
        # stores the terms in decides which generator is kept, not the constants needed
        @test shape(exp(x) + exp(x + 1), x) == [:exp]
        @test consts(exp(x) + exp(x + 1), x) == Set([G(:exp, 1)])
        @test consts(exp(x) + exp(x + 1//2), x) == Set([G(:exp, 1//2)])
        @test consts(exp(x) + exp(x + 1) + exp(x + 1//2), x) == Set([G(:exp, 1//2)])   # refined
        @test shape(log(x) + log(2x), x) == [:log]
        @test consts(log(x) + log(2x), x) == Set([G(:log, 2)])
        @test consts(log(x) + log(6x), x) == Set([G(:log, 2), G(:log, 3)])     # log 6 = log 2 + log 3
        @test consts(log(x) + log(x / 4), x) == Set([G(:log, 2)])              # log(1/4) = -2 log 2
        @test consts(log(x) + log(4x) + log(8x), x) == Set([G(:log, 2)])       # one generator
        @test shape(2^x, x) == [:exp] && consts(2^x, x) == Set([G(:log, 2)])  # exp(x log 2)
        @test shape(log(2x) - log(x), x) == Symbol[]                          # = log 2, a constant
    end

    @testset "$name: rejected input" begin
        @test_throws Risch.RischNotImplemented shape(sin(x), x)                 # needs Q(i), Stage 5
        @test_throws Risch.RischNotImplemented shape(sqrt(x), x)                # algebraic
        @test_throws Risch.RischNotImplemented shape(log(x) + log(-2x), x)      # log(-2): complex
        @test_throws Risch.RischNotImplemented shape(exp(x) + exp(x + log(x + 1) / 2), x)  # √(x+1)
    end
end

simple_x = let; SimpleExpressions.@symbolic x; x; end
sym_x = let; SymEngine.@vars x; x; end
run_tests(simple_x, (e, a) -> e isa Function ? e(a) : e, "SimpleExpressions")
run_tests(sym_x, (e, a) -> Float64(SymEngine.N(SymEngine.subs(e, sym_x => a))), "SymEngine")
