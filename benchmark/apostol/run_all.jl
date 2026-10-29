# julia run_all.jl [LIMIT]
# Runs the methods one after another (a cold start each) with a limit of
# LIMIT seconds per problem (default 120), then builds the page.
const HERE = @__DIR__
const LIMIT = get(ARGS, 1, "120")
mkpath(joinpath(HERE, "results"))

# the git commit of each package used from a local folder, and whether it has
# uncommitted changes (other than this run's results, which the run rewrites).
# Found before anything is written.
function commit(dir)
    try
        c = readchomp(`git -C $dir rev-parse --short HEAD`)
        changes = readchomp(`git -C $dir status --porcelain --untracked-files=no -- . ':(exclude)benchmark/apostol/results'`)
        c * (isempty(changes) ? "" : " (with uncommitted changes)")
    catch
        "unknown"
    end
end
# SymJ: the tip of its main branch, which env_symj is first updated to
run(`julia --project=$(joinpath(HERE, "env_symj")) -e 'using Pkg; Pkg.update("SymJ")'`)
symj = try
    readchomp(`git ls-remote https://github.com/jverzani/SymJ.jl refs/heads/main`)[1:7] * " (main)"
catch
    "unknown"
end
commits = [("RischIntegrate", commit(joinpath(HERE, "..", ".."))), ("SymJ", symj)]
open(joinpath(HERE, "results", "commits.tsv"), "w") do io
    foreach(((name, c),) -> println(io, name, "\t", c), commits)
end

for (name, env) in (("symengine", "env_risch"), ("expr", "env_risch"), ("symj", "env_symj"),
                    ("symbolicutils", "env_risch"), ("giac", "env_giac"), ("si_risch", "env_si"),
                    ("giac_own", "env_giac"))
    @info "running $name"
    run(`julia $(joinpath(HERE, "supervise.jl")) $name $env $LIMIT`)
end
run(`julia $(joinpath(HERE, "build.jl"))`)
