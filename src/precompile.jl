# step PC: a precompile workload on Expr terms. The first integral of a session otherwise spends
# seconds compiling the algebra over ℚ, ℚ(i), quadratic extensions and parameter fields, which is
# shared by every term type. Runs only while the package is precompiled.
@setup_workload begin
    expr_build = (op, args...) -> Expr(:call, nameof(op), args...)
    workload = [:(x * exp(x)), :(1 / (x^3 + 1)), :(1 / (x^5 + x + 1)), :(log(x)^2), :(1 / (1 + cos(x)^2)),
                :(exp(x) * sin(x)), :(x^2 * cos(x)), :(tan(x)), :(1 / (a^2 * sin(x)^2 + b^2 * cos(x)^2)),
                :(x / (x^2 + a)), :(sqrt(1 + 2x)), :(1 / sqrt(1 - x^2)), :(atan(x)), :(exp(x) / (exp(x) + 1)),
                :(1 / (x * log(x))), :(exp(-x^2)), :(sin(x) / x), :(log(log(x))), :(exp(a * x) * cos(b * x)),
                :(x * asin(x)),
                # (radicals, trig rational functions over ℚ(i), hyperelliptic and Kummer routes: added after
                # a report of first-use times of 1–2 s for ∫ 1/(5 + 2 sin x - cos x), ∫ √(3 - x²))
                :(1 / (5 + 2 * sin(x) - cos(x))), :(sqrt(3 - x^2)), :(sqrt(x^2 + 1)), :(x / sqrt(1 - x^4)),
                :(1 / (x^4 + 1)), :(sqrt(7 - 2 * x^2)), :(x * (x^3 + 1)^(1 // 3)), :(1 / sqrt(x^3 + 1)),
                :(sqrt(x) / (x - 1)), :(1 / (sin(x) + cos(x))), :(sqrt(1 + sin(x))), :(exp(x) * sqrt(1 - exp(2x))),
                :(log(x) / (1 + x)), :(1 / (x^2 * sqrt(x^2 - 1)))]
    @compile_workload begin
        for f in workload
            try
                risch_integrate(f, :x; build = expr_build, lift = identity)
            catch
            end
        end
    end
end
