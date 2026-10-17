# Shared by worker_giac.jl and worker_giac_own.jl: Giac variables and evaluation
using Giac
@giac_var x t a b c d z n
const VAR = Dict{Symbol,Any}(v => getfield(Main, v) for v in (:x, :t, :a, :b, :c, :d, :z, :n))
# evaluate by substituting each variable, then evalf. The values are rounded to 12 digits:
# Giac misreads a float such as 0.5700099999999999 (17 digits), giving undef or a wrong value.
r12(p::Real) = round(p, sigdigits = 12)
r12(p::Complex) = complex(r12(real(p)), r12(imag(p)))
function EVAL(ex, vals)
    ex isa Number && return complex(ex)
    u = to_julia(invoke_cmd(:evalf, Giac.substitute(ex, Dict(VAR[v] => r12(p) for (v, p) in vals))))
    isa(u, Number) ? complex(u) : nothing
end
