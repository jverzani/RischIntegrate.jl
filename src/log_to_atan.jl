# Rioboo's LogToAtan (Bronstein §2.8). For A, B ∈ K[x] (K real), B ≠ 0: polynomials p₁, …, pₖ with
#   Σ 2 atan(pⱼ)  ≡  2 atan(A/B)  ≡  i log((A + iB)/(A - iB))      (equal derivatives)
# Unlike atan(A/B), which jumps by ±π at the real zeros of B, a sum of atans of polynomials is
# continuous on the real line. Recursion: B | A gives A/B; deg A < deg B swaps to (-B, A);
# otherwise B D - A C = G = gcd(A, B) and 2 atan((A D + B C)/G) + LogToAtan(D, C).
function log_to_atan(A::UPoly{T}, B::UPoly{T}) where {T}
    out = UPoly{T}[]
    while true
        q, r = divrem(A, B)
        if iszero(r)
            push!(out, q)
            return out
        end
        if degree(A) < degree(B)
            A, B = -B, A
            continue
        end
        D, C, G = gcdex(B, -A)
        p, r = divrem(A * D + B * C, G)
        iszero(r) || throw(RischError("log_to_atan: G does not divide A D + B C"))
        push!(out, p)
        A, B = D, C
    end
end

# LogToAtan(U, √e V) for a real non-square e > 0 (the d < 0 case of a quadratic pair), without
# adjoining √e: under √e ↦ -√e, A = U is even and B = √e V odd, and this persists through the
# recursion, so every pⱼ = √e uⱼ and only the rational parts are needed. Two states:
#   even: A = a, B = √e b  (gcdex: e b d - a c = G; D = √e d, C = c; next: odd with (d, c))
#   odd:  A = √e a, B = b  (gcdex: b D - e a c = G; C = √e c;        next: even with (D, c))
# Returns [uⱼ] with Σ 2 atan(√e uⱼ) ≡ 2 atan(U/(√e V)). `ek` is e in the coefficient field, so
# this also works at a tower level (U, V ∈ K[θ]).
function log_to_atan_sqrt(a::UPoly{T}, b::UPoly{T}, ek::T) where {T}
    out = UPoly{T}[]
    even = true
    while true
        q, r = divrem(a, b)
        if iszero(r)                                    # A/B = √e·q/e (even) or √e·q (odd)
            push!(out, even ? scale(inv(ek), q) : q)
            return out
        end
        if degree(a) < degree(b)                        # (A, B) -> (-B, A)
            a, b = -b, a
            even = !even
            continue
        end
        if even
            d, c, G = gcdex(scale(ek, b), -a)
        else
            d, c, G = gcdex(b, -scale(ek, a))
        end
        u, r = divrem(a * d + b * c, G)                 # (A D + B C)/G = √e u in both states
        iszero(r) || throw(RischError("log_to_atan_sqrt: G does not divide the numerator"))
        push!(out, u)
        a, b = d, c
        even = !even
    end
end
