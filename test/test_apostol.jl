using Test
#using Giac
#@giac_var 𝑥 𝑡 𝑎 𝑏 𝑐 𝑑 𝑧 𝑛
#Base.://(a::GiacExpr, b::Int64) = a/b

using SimpleExpressions
SimpleExpressions.@symbolic_variables x t a  b c d z n
Base.://(a::SimpleExpressions.AbstractSymbolic, b::Int64) = a/b

import RischIntegrate

# these are from SymbolicIntegration.jl
apostol = [
    (sqrt(1 + (2 * x)), x),
    (x * sqrt(1 + (3 * x)), x),
    ((x ^ 2) * sqrt(1 + x), x),
    (x / sqrt(2 + (-3 * x)), x),
    ((1 + x) / ((2 + (x ^ 2) + (2 * x)) ^ 3), x),
    (sin(x) ^ 3, x),
(z * ((-1 + z) ^ 1//3), z),
(cos(x) / (sin(x) ^ 3), x),
(cos(2 * x) * sqrt(4 + (-1 * sin(2 * x))), x),
(sin(x) / ((3 + cos(x)) ^ 2), x),
(sin(x) / sqrt(cos(x) ^ 3), x),
(sin(sqrt(1 + x)) / sqrt(1 + x), x),
((x ^ (-1 + n)) * sin(x ^ n), x),
((x ^ 5) / sqrt(1 + (-1 * (x ^ 6))), x),
(t * ((1 + t) ^ 1//4), t),
(1 / ((1 + (x ^ 2)) ^ 3//2), x),
((x ^ 2) * ((27 + (8 * (x ^ 3))) ^ 2//3), x),
((sin(x) + cos(x)) / ((sin(x) + (-1 * cos(x))) ^ 1//3), x),
(x / sqrt(1 + (x ^ 2) + ((1 + (x ^ 2)) ^ 3//2)), x),
(x / (sqrt(1 + (x ^ 2)) * sqrt(1 + sqrt(1 + (x ^ 2)))), x),
(((1 + (x ^ 2) + (-2 * x)) ^ 1//5) / (1 + (-1 * x)), x),
(x * sin(x), x),
((x ^ 2) * sin(x), x),
((x ^ 3) * cos(x), x),
((x ^ 3) * sin(x), x),
(sin(x) * cos(x), x),
(x * sin(x) * cos(x), x),
(sin(x) ^ 2, x),
(sin(x) ^ 3, x),
(sin(x) ^ 4, x),
(sin(x) ^ 5, x),
(sin(x) ^ 6, x),
(x * (sin(x) ^ 2), x),
(x * (sin(x) ^ 3), x),
((x ^ 2) * (sin(x) ^ 2), x),
(cos(x) ^ 2, x),
(cos(x) ^ 3, x),
(cos(x) ^ 4, x),
(((a ^ 2) + (-1 * (x ^ 2))) ^ 5//2, x),
((x ^ 5) / sqrt(5 + (x ^ 2)), x),
((t ^ 3) / ((4 + (t ^ 3)) ^ 1//2), t),
(tan(x) ^ 2, x),
(tan(x) ^ 4, x),
(cot(x) ^ 2, x),
(cot(x) ^ 4, x),
((2 + (3 * x)) * sin(5 * x), x),
(x * sqrt(1 + (x ^ 2)), x),
(x * ((-1 + (x ^ 2)) ^ 9), x),
((3 + (2 * x)) / ((7 + (6 * x)) ^ 3), x),
((x ^ 4) * ((1 + (x ^ 5)) ^ 5), x),
((x ^ 4) * ((1 + (-1 * x)) ^ 20), x),
(sin(x ^ -1) / (x ^ 2), x),
(sin((-1 + x) ^ 1//4), x),
(x * sin(x ^ 2) * cos(x ^ 2), x),
(sqrt(1 + (3 * (cos(x) ^ 2))) * sin(2 * x), x),
(1 / (2 + (3 * x)), x),
(log(x) ^ 2, x),
(x * log(x), x),
(x * (log(x) ^ 2), x),
(1 / (1 + t), t),
(cot(x), x),
((x ^ n) * log(a * x), x),
((x ^ 2) * (log(x) ^ 2), x),
(1 / (x * log(x)), x),
(log(1 + (-1 * t)) / (1 + (-1 * t)), t),
(log(x) / (x * sqrt(1 + log(x))), x),
((x ^ 3) * (log(x) ^ 3), x),
((x ^ 2) * (ℯ ^ (x ^ 3)), x),
((2 ^ sqrt(x)) / sqrt(x), x),
(cos(x) * (ℯ ^ (2 * sin(x))), x),
((ℯ ^ x) * sin(x), x),
((ℯ ^ x) * cos(x), x),
(1 / (1 + (ℯ ^ x)), x),
(x * (ℯ ^ x), x),
(x * (ℯ ^ (-1 * x)), x),
((x ^ 2) * (ℯ ^ x), x),
((x ^ 2) * (ℯ ^ (-2 * x)), x),
(ℯ ^ sqrt(x), x),
((x ^ 3) * (ℯ ^ (-1 * (x ^ 2))), x),
((ℯ ^ (a * x)) * cos(b * x), x),
((ℯ ^ (a * x)) * sin(b * x), x),
(acot(x), x),
(asec(x), x),
(acsc(x), x),
(asin(x) ^ 2, x),
(asin(x) / (x ^ 2), x),
(1 / sqrt((a ^ 2) + (-1 * (x ^ 2))), x),
(1 / sqrt(1 + (-2 * x) + (-1 * (x ^ 2))), x),
(1 / ((a ^ 2) + (x ^ 2)), x),
(1 / (a + (b * (x ^ 2))), x),
(1 / (2 + (x ^ 2) + (-1 * x)), x),
(x * atan(x), x),
((x ^ 2) * acos(x), x),
(x * (atan(x) ^ 2), x),
(atan(sqrt(x)), x),
(atan(sqrt(x)) / (sqrt(x) * (1 + x)), x),
(sqrt(1 + (-1 * (x ^ 2))), x),
((x * (ℯ ^ atan(x))) / ((1 + (x ^ 2)) ^ 3//2), x),
((ℯ ^ atan(x)) / ((1 + (x ^ 2)) ^ 3//2), x),
((x ^ 2) / ((1 + (x ^ 2)) ^ 2), x),
((ℯ ^ x) / (1 + (ℯ ^ (2 * x))), x),
(acot(ℯ ^ x) / (ℯ ^ x), x),
(((a + x) / (a + (-1 * x))) ^ 1//2, x),
(sqrt((x + (-1 * a)) * (b + (-1 * x))), x),
(1 / sqrt((x + (-1 * a)) * (b + (-1 * x))), x),
((3 + (5 * x)) / (-3 + (x ^ 2) + (2 * x)), x),
((5 + (2 * x)) / (-3 + (x ^ 2) + (2 * x)), x),
(((x ^ 3) + (3 * x)) / (-3 + (x ^ 2) + (-2 * x)), x),
((-1 + (2 * (x ^ 2)) + (5 * x)) / ((x ^ 3) + (x ^ 2) + (-2 * x)), x),
((3 + (x ^ 2) + (2 * x)) / ((-1 + x) * ((1 + x) ^ 2)), x),
((-2 + (3 * (x ^ 2)) + (2 * x)) / (-1 + (x ^ 3)), x),
((2 + (x ^ 4) + (-1 * (x ^ 3)) + (2 * (x ^ 2)) + (-1 * x)) / ((-1 + x) * ((2 + (x ^ 2)) ^ 2)), x),
(1 / (sin(x) + cos(x)), x),
(x / (4 + (-1 * (x ^ 2)) + sqrt(4 + (-1 * (x ^ 2)))), x),
((3 + (2 * x)) / ((-2 + x) * (5 + x)), x),
(x / ((1 + x) * (2 + x) * (3 + x)), x),
(x / (2 + (x ^ 3) + (-3 * x)), x),
((-6 + (x ^ 4) + (2 * x)) / ((x ^ 3) + (x ^ 2) + (-2 * x)), x),
((7 + (8 * (x ^ 3))) / ((1 + x) * ((1 + (2 * x)) ^ 3)), x),
((1 + (4 * (x ^ 2)) + x) / (-1 + (x ^ 3)), x),
((x ^ 4) / (4 + (x ^ 4) + (5 * (x ^ 2))), x),
((2 + x) / ((x ^ 2) + x), x),
(1 / (x * ((1 + (x ^ 2)) ^ 2)), x),
(1 / ((1 + x) * ((2 + x) ^ 2) * ((3 + x) ^ 3)), x),
(x / ((1 + x) ^ 2), x),
(1 / ((x ^ 3) + (-1 * x)), x),
((x ^ 2) / (-6 + (x ^ 2) + x), x),
((2 + x) / (4 + (x ^ 2) + (-4 * x)), x),
(1 / ((4 + (x ^ 2) + (-4 * x)) * (5 + (x ^ 2) + (-4 * x))), x),
((-3 + x) / ((x ^ 3) + (3 * (x ^ 2)) + (2 * x)), x),
(1 / ((-1 + (x ^ 2)) ^ 2), x),
((1 + x) / (-1 + (x ^ 3)), x),
((1 + (x ^ 4)) / (x * ((1 + (x ^ 2)) ^ 2)), x),
(1 / ((x ^ 4) + (-2 * (x ^ 3))), x),
((1 + (-1 * (x ^ 3))) / (x * (1 + (x ^ 2))), x),
(1 / (-1 + (x ^ 4)), x),
(1 / (1 + (x ^ 4)), x),
((x ^ 2) / ((2 + (x ^ 2) + (2 * x)) ^ 2), x),
((-1 + (4 * (x ^ 5))) / ((1 + (x ^ 5) + x) ^ 2), x),
(1 / (5 + (2 * sin(x)) + (-1 * cos(x))), x),
(1 / (1 + (a * cos(x))), x),
(1 / (1 + (2 * cos(x))), x),
(1 / (1 + (cos(x) / 2)), x),
((sin(x) ^ 2) / (1 + (sin(x) ^ 2)), x),
(1 / (((a ^ 2) * (sin(x) ^ 2)) + ((b ^ 2) * (cos(x) ^ 2))), x),
(1 / (((a * sin(x)) + (b * cos(x))) ^ 2), x),
(sin(x) / (1 + sin(x) + cos(x)), x),
(sqrt(3 + (-1 * (x ^ 2))), x),
(x / sqrt(3 + (-1 * (x ^ 2))), x),
(sqrt(3 + (-1 * (x ^ 2))) / x, x),
(sqrt((x ^ 2) + x) / x, x),
(sqrt(5 + (x ^ 2)), x),
(x / sqrt(1 + (x ^ 2) + x), x),
(1 / sqrt((x ^ 2) + x), x),
(sqrt(2 + (-1 * x) + (-1 * (x ^ 2))) / (x ^ 2), x),
(log(t) / (1 + t), t),
(log(ℯ ^ cos(x)), x),
((ℯ ^ t) / t, t),
((ℯ ^ (a * t)) / t, t),
((ℯ ^ t) / (t ^ 2), t),
(ℯ ^ (t ^ -1), t),
(1 / ((ℯ ^ t) * (-1 + t + (-1 * a))), t),
((t * (ℯ ^ (t ^ 2))) / (1 + (t ^ 2)), t),
((ℯ ^ t) / ((1 + t) ^ 2), t),
((ℯ ^ t) * log(1 + t), t),
(t / (ℯ ^ t), t),
((t ^ 2) / (ℯ ^ t), t),
((t ^ 3) / (ℯ ^ t), t),
(((c * sin(x)) + (d * cos(x))) / ((a * sin(x)) + (b * cos(x))), x),
(1 / log(t), t),
(1 / (log(t) ^ 2), t),
(1 / (log(t) ^ (1 + n)), t),
((ℯ ^ (2 * t)) / (-1 + t), t),
((ℯ ^ (2 * x)) / (2 + (x ^ 2) + (-3 * x)), x),
    (1 / ((1 + (t ^ 3)) ^ 1//2), t),
]

#=
function se_to_giac(fx)
    m = [x t a  b c d z n] .=> [𝑥 𝑡 𝑎 𝑏 𝑐 𝑑 𝑧 𝑛]
    D = Dict(m...)
    F,X = fx
    𝐹 = F(m...)();
    𝑋 = D[X]
    (𝐹, 𝑋)
end

apostolg = se_to_giac.(apostol)

function giac_integration_success(fx)
    f,x = fx
    risch = try
        F = Giac.Commands.integrate(f,x)
        @show F, diff(F,x), f
        return iszero(Giac.Commands.simplify(diff(F,x))- f)
    catch err
        f
    end
end
=#

function se_integration_success(fs)
    f,x = fs
    risch = try
        RischIntegrate.integrate(f,x)
        true
    catch err
        #@show :f, f
        #@show err
        false
    end
end

@testset "apostol problems" begin
    @test sum(se_integration_success, apostol) >= 160
end



#=

function compare_integrate(fs)
    f,F,x,_ = fs

    rules = try
        F = RUBISymbolicIntegration.integrate(f, x)
        !RUBISymbolicIntegration.contains_int(F)
    catch err
        @show err
        false
    end

    risch = try
        F = RischIntegrate.integrate(f,x)
        true
    catch err
        @show err
        false
    end

    (;rules, risch)
end

function integration_test(fs)
    f,F,x,_ = fs
    risch = try
        F = RischIntegrate.integrate(f,x)
        F
    catch err
        false
    end

    risch != false && return risch

    F′ = RUBISymbolicIntegration.integrate(f, x)

    RUBISymbolicIntegration.contains_int(F′) ? (return nothing) : F′


end

# What F doesn't integrate
# started with 101
# SE: 131 integrate successfully
# SE: 134 integrate successfully (with cot, csc,sec)
# giac 172 integrate successfully
function integration_failures(fs)
    f,F,x,_ = fs
    risch = try
        RischIntegrate.integrate(f,x)
        nothing
    catch err
        @show :f, f
        @show err
        f
    end
end

using TermInterface: isexpr, operation, arguments, maketerm
function replace_op(ex, opmap)
    !isexpr(ex) && return ex
    op, args = operation(ex), arguments(ex)
    𝑜𝑝 = haskey(opmap, op) ? opmap[op] : op
    return maketerm(typeof(ex), 𝑜𝑝, replace_op.(args, (opmap,)), nothing)
end
=#
