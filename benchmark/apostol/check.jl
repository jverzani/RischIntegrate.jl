# julia check.jl BASELINE RESULTS NAME...
# Compares the verified problems of each method NAME in RESULTS/results_NAME.tsv with those of the
# committed run in BASELINE/results_NAME.tsv. Prints the counts and the problems verified before and
# not now (and the reverse); exits with 1 if any method lost a verified problem.
verified(file) = Set(parse(Int, r[2]) for r in (split(l, '\t') for l in eachline(file))
                     if r[1] == "R" && length(r) >= 4 && r[4] == "verified")
const BASE, NEW = ARGS[1], ARGS[2]
lost_any = false
for name in ARGS[3:end]
    global lost_any
    b = verified(joinpath(BASE, "results_$name.tsv"))
    n = verified(joinpath(NEW, "results_$name.tsv"))
    lost, gained = sort!(collect(setdiff(b, n))), sort!(collect(setdiff(n, b)))
    println(rpad(name, 16), length(n), " verified (committed run: ", length(b), ")")
    isempty(lost) || println("  no longer verified: ", join(lost, ", "))
    isempty(gained) || println("  newly verified: ", join(gained, ", "))
    for l in eachline(joinpath(NEW, "results_$name.tsv"))
        r = split(l, '\t')
        r[1] == "R" && parse(Int, r[2]) in lost && println("    ", join(r[2:min(end, 6)], "  ")[1:min(end, 200)])
    end
    lost_any |= !isempty(lost)
end
exit(lost_any ? 1 : 0)
