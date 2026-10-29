# julia build.jl
# Builds results/apostol_comparison.html from results/*.tsv and template.html
const HERE = @__DIR__
const RESULTS = joinpath(HERE, "results")
const METHODS = [
    ("symengine", "RischIntegrate", "Risch", "SymEngine"),
    ("expr", "RischIntegrate", "Risch", "Expr"),
    ("symj", "RischIntegrate", "Risch", "SymJ"),
    ("symbolicutils", "RischIntegrate", "Risch", "SymbolicUtils"),
    ("giac", "RischIntegrate", "Risch", "Giac"),
    ("si_risch", "SymbolicIntegration", "Risch (RischMethod)", "Symbolics"),
    ("giac_own", "Giac", "Giac's integrate (for reference)", "Giac"),
]

# a small JSON writer, enough for the page's data
json(x::Nothing) = "null"
json(x::Bool) = string(x)
json(x::Real) = isfinite(x) ? string(x) : "null"
function json(s::AbstractString)
    io = IOBuffer(); print(io, '"')
    for c in s
        c == '"' ? print(io, "\\\"") : c == '\\' ? print(io, "\\\\") :
        c == '<' ? print(io, "\\u003c") : c < ' ' ? print(io, "\\u", string(UInt16(c), base = 16, pad = 4)) : print(io, c)
    end
    print(io, '"'); String(take!(io))
end
json(v::AbstractVector) = "[" * join(json.(v), ",") * "]"
json(d::AbstractDict) = "{" * join((json(string(k)) * ":" * json(v) for (k, v) in d), ",") * "}"

problems = [Dict("i" => i, "x" => string(x), "f" => string(ex))
            for (i, (ex, x)) in enumerate(include(joinpath(HERE, "problems.jl")))]
N = length(problems)

versions = Dict{String,String}("Julia" => string(VERSION))
methods = map(METHODS) do (key, pkg, method, terms)
    cells = Vector{Any}(nothing, N)
    loads, wall, limit = Float64[], nothing, nothing
    for line in eachline(joinpath(RESULTS, "results_$key.tsv"))
        p = split(line, '\t')
        if p[1] == "R"
            cells[parse(Int, p[2])] = Dict("s" => p[3], "v" => p[4], "t" => round(parse(Float64, p[5]), digits = 3),
                                           "o" => length(p) > 5 ? p[6] : "")
        elseif p[1] == "L"
            push!(loads, parse(Float64, p[2]))
        elseif p[1] == "T"
            wall = parse(Float64, p[2])
            limit = parse(Float64, p[3])
        elseif p[1] == "V"
            versions[p[2]] = p[3]
        end
    end
    missing = findall(isnothing, cells)
    isempty(missing) || error("$key: no result for problems $missing")
    Dict("key" => key, "pkg" => pkg, "method" => method, "terms" => terms, "cells" => cells,
         "load" => isempty(loads) ? nothing : round(first(loads), digits = 2),
         "restarts" => max(length(loads) - 1, 0),
         "integration" => round(sum(c["t"] for c in cells), digits = 1),
         "wall" => wall === nothing ? nothing : round(wall, digits = 1), "limit" => limit)
end

commits = Dict{String,String}()
f = joinpath(RESULTS, "commits.tsv")
isfile(f) && for line in eachline(f)
    k, v = split(line, '\t'); commits[k] = v
end
date = Libc.strftime("%Y-%m-%d", isfile(f) ? mtime(f) : time())

data = Dict("problems" => problems, "methods" => methods, "date" => date,
            "limit" => maximum(something(m["limit"], 0) for m in methods),
            "versions" => versions, "commits" => commits)
html = replace(read(joinpath(HERE, "template.html"), String), "/*DATA*/null" => json(data))
write(joinpath(RESULTS, "apostol_comparison.html"), html)

for m in methods
    k = map(m["cells"]) do c
        c["s"] == "solved" ? c["v"] : c["s"]
    end
    counts = sort([(s, count(==(s), k)) for s in unique(k)], by = last, rev = true)
    println(rpad(m["key"], 18), " ", join(("$s $n" for (s, n) in counts), ", "),
            " | integration $(m["integration"]) s, load $(m["load"]) s, wall $(m["wall"]) s")
end
