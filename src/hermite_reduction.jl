# ---------------------------------------------------------------------------
# Differential structure of ℚ(x): d/dx
# ---------------------------------------------------------------------------
const CX = UPoly{C}              # C[x]
const CXF = Frac{CX}             # C(x), the base field K_0
const QX = CX                    # legacy names, kept for the tests and external callers
const QXF = CXF

# d/dx on the base level (valid ONLY for elements of C(x): at higher levels use D(T, i, f))
dx(p::UPoly) = deriv(p)
dx(f::Frac{<:UPoly}) = frac(deriv(f.num) * f.den - f.num * deriv(f.den), f.den * f.den)
kconst(c::T) where {T} = frac(UPoly{T}(T[c]))       # constant c as an element of C(x)

function integrate_poly(p::UPoly{T}) where {T}
    iszero(p) && return p
    UPoly{T}(T[i == 1 ? zero(T) : p.c[i - 1] / ((i - 1) * one(T)) for i in 1:(length(p.c) + 1)])
end

# ---------------------------------------------------------------------------
# Hermite reduction (Bronstein, Alg. 2.2 / 5.x), for a derivation δ on K[θ]:
#   A/D  =  Q  +  (g)'  +  R/Dsf
# with Q polynomial, g the rational part, Dsf squarefree. Returns (g, Q, R, Dsf).
# ---------------------------------------------------------------------------
function hermite_reduce(δ, A::P, D::P) where {P<:UPoly}
    Qp, R = divrem(A, D)
    g = zero(Frac{P})
    for (V, m) in squarefree(D)
        m >= 2 || continue
        for j in (m - 1):-1:1
            Dstar = quo(D, V^(j + 1))
            dV = δ(V)
            s, _, gg = gcdex(Dstar * dV, V)
            isone(gg) || throw(RischError("Hermite reduction: gcd(D*V', V) != 1"))
            B = rem(s * R, V)
            Cq = quo(R - B * Dstar * dV, V)
            g = g + frac(-B, j * V^j)
            R = Cq + Dstar * divint(δ(B), j)              # A ← C + U B'/j (U = D*)
            D = quo(D, V)
        end
    end
    g, Qp, R, D
end
