# The apostol problems as (integrand, variable) expressions, parsed (not
# evaluated) from the test suite, so each worker builds them with its own
# variables
let src = read(joinpath(@__DIR__, "..", "..", "test", "test_apostol.jl"), String)
    ex = Meta.parse("begin\n" * src * "\nend")
    vect = only(a.args[2] for a in ex.args if Meta.isexpr(a, :(=)) && a.args[1] === :apostol)
    [(t.args[1], t.args[2]) for t in vect.args]
end
