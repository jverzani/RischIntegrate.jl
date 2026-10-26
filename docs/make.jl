using Documenter, MaterialDocs
using RischIntegrate

makedocs(
    sitename = "RischIntegrate.jl",
    modules = [RischIntegrate],
    checkdocs = :exports,
    warnonly = [:missing_docs],          # the module docstring is the README
    format = Material3(theme = :default, dark_mode = :toggle, prettyurls = get(ENV, "CI", nothing) == "true", edit_link = "main"),
    pages = [
        "Home" => "index.md",
        "Usage" => "usage.md",
        "How it works" => "algorithm.md",
        "Design notes" => "design.md",
        "Reference" => "reference.md",
    ],
)

deploydocs(repo = "github.com/jverzani/RischIntegrate.jl.git", devbranch = "main", push_preview = true)
