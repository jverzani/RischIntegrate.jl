# Shared by the workers. Before including, a worker defines:
#   VAR::Dict{Symbol,Any}   the symbolic variables
#   INTEGRATE(f, x)          the method being compared
#   SOLVED(out)::Bool        did it return an antiderivative?
#   TOSU(ex)                 a SymbolicUtils term, for checking; or instead
#   EVAL(ex, vals)           the value of `ex` with each variable `v` replaced by
#                            `vals[v]`, as a number, or `nothing`
#   BUILD(ex)                (optional) the integrand from the problem's expression;
#                            by default the expression evaluated with VAR's variables
# Usage: julia --project=ENV worker_X.jl START OUTFILE (run by supervise.jl)
const T_LOADED = time()

const PROBLEMS = include(joinpath(@__DIR__, "problems.jl"))
const ALLVARS = (:x, :t, :a, :b, :c, :d, :z, :n)

# the integrand, built with this worker's variables
function build(ex)
    m = Module()
    for v in ALLVARS
        Core.eval(m, :(const $v = $(VAR[v])))
    end
    Core.eval(m, ex)
end

# ---- numeric check: d/dx F == f at two points, parameters fixed
const PARAMS = Dict(v => 1.0 + 0.137 * i for (i, v) in enumerate(ALLVARS))

# the default EVAL, through SymbolicUtils (loaded by a worker that defines TOSU)
function su_eval(ex, vals)
    d = Dict{Any,Any}(TOSU(VAR[v]) => p for (v, p) in vals)
    r = SymbolicUtils.substitute(TOSU(ex), d; fold = Val(true))
    u = SymbolicUtils.unwrap_const(r)
    isa(u, Number) ? complex(u) : nothing
end
isdefined(@__MODULE__, :EVAL) || (EVAL(ex, vals) = su_eval(ex, vals))
isdefined(@__MODULE__, :BUILD) || (BUILD(ex) = build(ex))

# RischIntegrate's answer with RootSums evaluates at a real value of the variable
is_rootsums(e) = nameof(typeof(e)) === :IntegralWithRootSums

function evalat(e, xs, x0, cplx)
    is_rootsums(e) && return cplx ? error("real values only") : complex(e(x0))
    vals = Dict{Symbol,Number}()
    for v in ALLVARS
        p = v === xs ? x0 : PARAMS[v]
        vals[v] = cplx ? complex(p) : p
    end
    EVAL(e, vals)
end

# the check points: 0.31 and 0.57, except that a point where the integrand is not real (outside its real
# domain, where an answer may be on a branch cut: asin(u) for u > 1) is replaced by a spare real point
# where it is; complex values are used only where there is none
const POINTS = (0.31, 0.57)
const SPARE = (0.13, -0.43, 0.83, -0.77, 1.37, -1.61, 2.11, -2.3, 3.3)
function realat(f, xs, x0)
    v = try evalat(f, xs, x0, false) catch; nothing end
    v !== nothing && isfinite(v) && abs(imag(v)) <= 1e-12 * max(1, abs(v))
end
function check_points(f, xs)
    pts, spare = Float64[], collect(SPARE)
    for x0 in POINTS
        i = realat(f, xs, x0) ? nothing : findfirst(s -> realat(f, xs, s), spare)
        push!(pts, i === nothing ? x0 : popat!(spare, i))
    end
    pts
end

function check(f, F, xs)
    fsu, Fsu = f, F
    for x0 in check_points(f, xs)
        h = 1e-5
        ok = nothing
        for cplx in (false, true)
            vals = try
                (evalat(fsu, xs, x0, cplx), evalat(Fsu, xs, x0 + h, cplx), evalat(Fsu, xs, x0 - h, cplx))
            catch
                nothing
            end
            vals === nothing && continue
            any(isnothing, vals) && return :unverified
            fv, Fp, Fm = vals
            (isfinite(fv) && isfinite(Fp) && isfinite(Fm)) || continue
            dF = (Fp - Fm) / (2h)
            ok = abs(dF - fv) <= 1e-4 * max(1, abs(fv))
            break
        end
        ok === nothing && return :unverified
        ok || return :wrong
    end
    return :verified
end

clean(s) = replace(s, r"\s+" => " ")[1:min(end, 400)]

function run_one(io, i)
    ex, xs = PROBLEMS[i]
    println(io, "S\t$i\t", time()); flush(io)
    f = BUILD(ex)
    x = VAR[xs]
    t0 = time()
    out = try
        INTEGRATE(f, x)
    catch err
        err
    end
    dt = time() - t0
    if out isa Exception
        status, ver, s = :error, :none, sprint(showerror, out)
    elseif SOLVED(out)
        status, s = :solved, string(out)
        ver = try check(f, out, xs) catch; :unverified end
    else
        status, ver, s = :unsolved, :none, string(out)
    end
    println(io, "R\t$i\t$status\t$ver\t$dt\t", clean(s)); flush(io)
    dt
end

let start = parse(Int, ARGS[1]), outfile = ARGS[2]
    open(outfile, "a") do io
        println(io, "L\t", T_LOADED - T_START, "\t", start); flush(io)
        start == 1 && for (k, m) in Base.loaded_modules
            k.name in ("RischIntegrate", "SymbolicIntegration", "Symbolics", "SymbolicUtils",
                       "SymJ", "SymEngine", "Giac") || continue
            println(io, "V\t", k.name, "\t", pkgversion(m))
        end
        foreach(i -> run_one(io, i), start:length(PROBLEMS))
        println(io, "D"); flush(io)
    end
end
