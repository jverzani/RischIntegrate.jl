using Documenter
using RischIntegrate

makedocs(
    sitename = "RischIntegrate.jl",
    modules = [RischIntegrate],
    checkdocs = :exports,
    warnonly = [:missing_docs],          # the module docstring is the README
    format = Documenter.HTML(prettyurls = get(ENV, "CI", nothing) == "true", edit_link = "main"),
    pages = [
        "Home" => "index.md",
        "Usage" => "usage.md",
        "How it works" => "algorithm.md",
        "Reference" => "reference.md",
    ],
)

deploydocs(repo = "github.com/jverzani/RischIntegrate.jl.git", devbranch = "main", push_preview = true)
