const T_START = time()
using SymbolicUtils
using SymbolicUtils: @syms
import RischIntegrate
@syms x::Real t::Real a::Real b::Real c::Real d::Real z::Real n::Real
const VAR = Dict{Symbol,Any}(v => getfield(Main, v) for v in (:x, :t, :a, :b, :c, :d, :z, :n))
INTEGRATE(f, x) = RischIntegrate.integrate(f, x)
SOLVED(out) = true  # failures throw
TOSU(ex) = ex
include("core.jl")
