const T_START = time()
using Symbolics, SymbolicUtils
using SymbolicIntegration
@variables x t a b c d z n
const VAR = Dict{Symbol,Any}(v => getfield(Main, v) for v in (:x, :t, :a, :b, :c, :d, :z, :n))
INTEGRATE(f, x) = integrate(f, x, RischMethod())
SOLVED(out) = !occursin("∫", string(out))
TOSU(ex) = Symbolics.unwrap(ex)
include("core.jl")
