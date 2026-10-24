using Test

# Calls of integrate from compiled code (the definite integral, a user's function) must not infer the whole
# integrator for the term type (@nospecializeinfer on integrate and risch_integrate): ~20 s in a fresh
# session without it, well under a second with it. Timed in a new process, after a first top-level call.
@testset "first calls from compiled code" begin
    code = """
        using SymEngine: @vars
        using RischIntegrate: integrate, risch_integrate
        @vars x
        integrate(sin(x), x)
        user(ex, x) = integrate(ex, x)
        user2(ex, x) = risch_integrate(ex, x)
        t = @elapsed (integrate(sin(x), (x, 0, pi)), user(cos(x), x), user2(sin(x), x))
        print(t)
        """
    # the test's own environment (under Pkg.test a temporary one, not test/)
    out = read(`$(Base.julia_cmd()) --startup-file=no --project=$(Base.active_project()) -e $code`, String)
    t = parse(Float64, strip(out))
    @test t < 10                                        # (CI runners, coverage)
end
