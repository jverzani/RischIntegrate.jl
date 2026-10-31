# --- printing and numeric evaluation ---------------------------------------------
function zpoly_string(p::UPoly, v::String)
    ts = String[]
    for (k, c) in enumerate(p.c)
        iszero(c) && continue
        mon = k == 1 ? "" : (k == 2 ? v : "$v^$(k - 1)")
        cs = c isa Rational ? (isone(denominator(c)) ? string(numerator(c)) :
                               "$(numerator(c))/$(denominator(c))") :
             c isa QI ? (iszero(c.im) ? zpoly_string(UPoly{Q}([c.re]), "") :
                         "(" * zpoly_string(UPoly{Q}([c.re, c.im]), "im") * ")") : string(c)
        push!(ts, mon == "" ? cs : (isone(c) ? mon : (c == -1 ? "-" * mon : cs * "*" * mon)))
    end
    isempty(ts) ? "0" : replace(join(reverse(ts), " + "), "+ -" => "- ")
end
function Base.show(io::IO, rs::RootSum)
    x = rs.var
    ts = String[]
    for (k, c) in enumerate(rs.W)
        iszero(c) && continue
        cs = zpoly_string(c, "α")
        mon = k == 1 ? "" : (k == 2 ? x : "$x^$(k - 1)")
        push!(ts, mon == "" ? "($cs)" : (isone(c) ? mon : "($cs)*$mon"))
    end
    print(io, "RootSum(α -> α*log(", join(reverse(ts), " + "), "), ", zpoly_string(rs.poly, "α"), " = 0)")
end
function Base.show(io::IO, F::IntegralWithRootSums)
    ts = Any[rs for rs in F.rootsums]
    string(F.elementary) == "0" || pushfirst!(ts, F.elementary)
    # a part with a leading minus sign after " - ", not " + -1 * " (-1 * clausen2(x - π))
    for (i, t) in enumerate(ts)
        s = string(t)
        if i == 1
            print(io, s)
        elseif startswith(s, "-1 * ")
            print(io, " - ", s[6:end])
        elseif startswith(s, "-")
            print(io, " - ", s[2:end])
        else
            print(io, " + ", s)
        end
    end
end

# all complex roots of a polynomial with complex coefficients (Aberth–Ehrlich iteration)
function numeric_roots(cs::Vector{ComplexF64})
    n = length(cs) - 1
    cs = cs ./ cs[end]
    r = 1 + maximum(abs.(cs[1:n]))
    zs = [r * cis(2π * (k + 0.25) / n) for k in 0:(n - 1)]
    pv(z) = foldr((c, acc) -> acc * z + c, cs)
    dv(z) = foldr((c, acc) -> acc * z + c, [k * cs[k + 1] for k in 1:n]; init = 0.0im)
    for _ in 1:500
        δmax = 0.0
        for i in 1:n
            z = zs[i]
            w = pv(z) / dv(z)
            s = sum(1 / (z - zs[j]) for j in 1:n if j != i; init = 0.0im)
            δ = w / (1 - w * s)
            zs[i] = z - δ
            δmax = max(δmax, abs(δ))
        end
        δmax < 1e-15 * r && break
    end
    zs
end

cnum(c::Q) = ComplexF64(Float64(c))
cnum(c::QI) = ComplexF64(Float64(c.re), Float64(c.im))
cnum(c) = throw(RischNotImplemented("numeric evaluation of constants of type $(typeof(c))"))
cpoly_at(p::UPoly, z) = foldr((c, acc) -> acc * z + cnum(c), p.c; init = 0.0im)

function (rs::RootSum)(a::Number)
    tot = 0.0im
    for α in numeric_roots(ComplexF64[cnum(c) for c in rs.poly.c])
        w = foldr((c, acc) -> acc * a + cpoly_at(c, α), rs.W; init = 0.0im)
        tot += α * log(w)
    end
    tot
end

# numeric value of a term of the user's package at x = a (TermInterface walk)
function term_value(t, xk::String, a)
    if safe_iscall(t)
        args = arguments(t)
        if !isempty(args)
            vs = [term_value(s, xk, a) for s in args]
            f = op_function(t)
            return ComplexF64(f(vs...))
        end
    end
    string(t) == xk && return ComplexF64(a)
    is_e_const(t) && return ComplexF64(ℯ)
    string(t) in ("pi", "π") && return ComplexF64(π)
    r = leaf_rational(t)
    r === nothing && throw(RischError("cannot evaluate the leaf $t numerically"))
    ComplexF64(Float64(r))
end

function Base.show(io::IO, rs::TermRootSum)
    ts = String[]
    for (j, c) in enumerate(rs.coeffs)
        c isa Tuple && (c = coeff_string(c))
        c === nothing && continue
        push!(ts, j == 1 ? "($c)" : (j == 2 ? "($c)*α" : "($c)*α^$(j - 1)"))
    end
    ps = rs.pterms === nothing ? zpoly_string(rs.poly, "α") :
         join(reverse([k == 1 ? "($t)" : (isone(rs.poly.c[k]) ? "" : "($t)*") * (k == 2 ? "α" : "α^$(k - 1)")
                       for (k, t) in enumerate(rs.pterms) if !iszero(rs.poly.c[k])]), " + ")
    print(io, "RootSum(α -> α*log(", join(ts, " + "), "), ", ps, " = 0)")
end
# numeric coefficients of the RootSum polynomial
rs_poly_numeric(rs::TermRootSum, xk::String) =
    rs.pterms === nothing ? ComplexF64[cnum(c) for c in rs.poly.c] : ComplexF64[term_value(t, xk, 0.0) for t in rs.pterms]
coeff_string((r, i)::Tuple) = (r === nothing && i === nothing) ? nothing :
    join(filter(!isempty, [r === nothing ? "" : string(r), i === nothing ? "" : "im*($i)"]), " + ")
cvalue(c, xk, a) = c === nothing ? 0.0im :
    c isa Tuple ? cvalue(c[1], xk, a) + im * cvalue(c[2], xk, a) : term_value(c, xk, a)
function rs_value(rs::TermRootSum, xk::String, a)
    vs = [cvalue(c, xk, a) for c in rs.coeffs]
    tot = 0.0im
    for α in numeric_roots(rs_poly_numeric(rs, xk))
        tot += α * log(foldr((v, acc) -> acc * α + v, vs; init = 0.0im))
    end
    tot
end
rs_value(rs::RootSum, xk::String, a) = rs(rs.arg === nothing ? a : term_value(rs.arg, xk, a))
(rs::TermRootSum)(a::Number) = rs_value(rs, rs.var, a)

# --- continuous evaluation (step RN) -----------------------------------------------
# A principal log W(α, x) jumps by 2πi where W crosses the negative real axis, and α·2πi then
# shifts Re F by -2π Im α. F(a) instead continues each log along [x₀, a] from a fixed reference
# point x₀ (the first of a few candidates where every W is finite and nonzero): the phase change
# is accumulated in steps refined until each is < 0.5 rad. This changes F only by constants on
# intervals, so it is still an antiderivative, now continuous.

# numeric roots α and a closure x -> [W(α, x) for each α]
function rs_numeric(rs::RootSum, xk::String)
    αs = numeric_roots(ComplexF64[cnum(c) for c in rs.poly.c])
    Wf(x) = (t = rs.arg === nothing ? ComplexF64(x) : term_value(rs.arg, xk, x);
             [foldr((c, acc) -> acc * t + cpoly_at(c, α), rs.W; init = 0.0im) for α in αs])
    αs, Wf
end
function rs_numeric(rs::TermRootSum, xk::String)
    αs = numeric_roots(rs_poly_numeric(rs, xk))
    Wf(x) = (vs = [cvalue(c, xk, x) for c in rs.coeffs];
             [foldr((v, acc) -> acc * α + v, vs; init = 0.0im) for α in αs])
    αs, Wf
end

const RS_REFERENCE_POINTS = (1.0, 2.0, 0.5, 3.0, 0.0, -1.0, 5.0, 10.0)

w_ok(w) = all(z -> isfinite(z) && abs(z) > 1e-12, w)
function safe_W(Wf, x)
    try
        Wf(x)
    catch
        nothing
    end
end

# phases of W(α, ·) continued from s (phases θ, values ws) to t
function continue_phase(Wf, s, t, ws, θ, depth::Int = 0)
    wt = safe_W(Wf, t)
    # a zero of W on the path is a pole of the integrand (F has a log singularity there): step over it
    (wt === nothing || !w_ok(wt)) && return θ, ws
    d = angle.(wt ./ ws)
    if maximum(abs, d) > 0.5 && depth < 40
        m = (s + t) / 2
        θ, wm = continue_phase(Wf, s, m, ws, θ, depth + 1)
        return continue_phase(Wf, m, t, wm, θ, depth + 1)
    end
    θ .+ d, wt
end

function rs_value_continuous(rs, xk::String, a::Real)
    αs, Wf = rs_numeric(rs, xk)
    x0 = nothing
    w0 = nothing
    for c in RS_REFERENCE_POINTS
        w = safe_W(Wf, c)
        if w !== nothing && w_ok(w)
            x0, w0 = c, w
            break
        end
    end
    x0 === nothing && return rs_value(rs, xk, a)        # no reference point found: principal logs
    θ, w = angle.(w0), w0
    n = max(8, ceil(Int, 8 * abs(a - x0)))
    xs = range(x0, a; length = n + 1)
    for k in 2:length(xs)
        θ, w = continue_phase(Wf, xs[k - 1], xs[k], w, θ)
    end
    sum(αs[k] * (log(abs(w[k])) + im * θ[k]) for k in eachindex(αs); init = 0.0im)
end

(F::IntegralWithRootSums)(a::Real) =
    real(term_value(F.elementary, F.var, a) +
         sum(rs_value_continuous(rs, F.var, a) for rs in F.rootsums; init = 0.0im))
# substitution syntax `F(x => value)` with a numeric value (definite integrals `F(x => b) - F(x => a)`)
function (F::IntegralWithRootSums)(p::Pair)
    (string(p.first) == F.var && p.second isa Real) || throw(RischNotImplemented(
        "an IntegralWithRootSums can only be evaluated at a numeric value of $(F.var)"))
    F(p.second)
end
