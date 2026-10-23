# Step DL: dilogarithms. ∫ θ·r(x) with θ = log(a x + b) (a level over ℚ(x) only, a, b ∈ ℚ) and r ∈ ℚ(x):
# each simple pole c ∈ ℚ of r with residue ρ and K = a c + b ≠ 0 gives (s = x - c, a s + K = a x + b)
#   K > 0:  ρ (log K · log|s| - Li₂(-a s/K))          (log(K + a s) = log K + log(1 + a s/K))
#   K < 0:  ρ (½ log²(a s) + Li₂(-K/(a s)))            (log(K + a s) = log(a s) + log(1 - |K|/(a s)))
# both with derivative ρ θ/(x - c) on the domain a x + b > 0 (Li₂(z)' = -log(1 - z)/z). The term
# keeps that derivative for the exact check (as SpecialTerm); the rest of the integrand goes through
# the normal algorithm. Printed with `PolyLog.li2`, which the symbolic package must support.
# (ρ, a, b, c in the constant field: ℚ, or a parameter field ℚ(a, …) (∫ log(x)/(a + bx)); there the sign
# of K is taken at the parameter values of `param_value`, a = 1, b = 2, …, as for the step PQ forms)
struct DilogTerm
    ρ::Any
    a::Any
    b::Any
    c::Any
    deriv::Any
end
function dilog_split(T::Tower, i::Int, p::UPoly)
    C = ctype(T)
    ((C === Q || real_param_field(C)) && i == 1 && T.levels[1].kind === :log && degree(p) == 1) || return nothing
    u = T.levels[1].arg
    (isone(u.den) && degree(u.num) == 1) || return nothing
    b, a = u.num.c
    r = p.c[2]                                          # coefficient of θ, ∈ ℚ(x)
    D1 = r.den
    terms = Any[]
    simple = zero(r)
    xp = xpoly(Q)
    θ = frac(xpoly(T.Ts[1]))
    for c in constant_roots(D1)
        lin = UPoly{C}(C[-c, one(C)])
        iszero(rem(D1, lin * lin)) && continue           # not a simple pole
        K = a * c + b
        iszero(K) && continue                            # log(a s)/s: elementary
        ρ = peval(r.num, c) / peval(deriv(D1), c)
        iszero(ρ) && continue
        rs = frac(UPoly{C}(C[ρ]), lin)
        simple = simple + rs
        push!(terms, DilogTerm(ρ, a, b, c, liftto(T, rs, 1) * θ))
    end
    isempty(terms) && return nothing
    P = typeof(p)
    (P(eltype(p.c)[p.c[1], r - simple]), terms)
end

function dilog_term(b::Builder, q::DilogTerm)
    C = typeof(q.c)
    st = poly_term(b, UPoly{C}(C[-q.c, one(C)]))       # s = x - c
    K = q.a * q.c + q.b
    li(z) = mk(b, :li2, z)          # a MethodError if the symbolic package has no method for li2
    Kr = crational(K)
    Kpos = Kr !== nothing ? Kr > 0 : (v = param_value(K, b.consts); v !== nothing && v > 0)
    if Kpos
        L = li(mk(b, :*, cterm(b, -q.a / K), st))
        core = isone(K) ? mk(b, :*, b.lift(-1), L) :           # log K · ½ log(s²) - Li₂(-a s/K)
               mk(b, :+, mk(b, :*, cterm(b, Q(1) // 2), mk(b, :log, cterm(b, K)), mk(b, :log, mk(b, :^, st, b.lift(2)))),
                  mk(b, :*, b.lift(-1), L))
    else
        as = isone(q.a) ? st : mk(b, :*, cterm(b, q.a), st)
        core = mk(b, :+, mk(b, :*, cterm(b, Q(1) // 2), mk(b, :^, mk(b, :log, as), b.lift(2))),
                  li(mk(b, :/, cterm(b, -K), as)))
    end
    isone(q.ρ) ? core : mk(b, :*, cterm(b, q.ρ), core)
end
