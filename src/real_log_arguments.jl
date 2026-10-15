# steps RL, EL: the logs of a rational integral in t, real at the real points of a substitution:
# the t with every φ ∈ pos positive (10a: t = u^(1/n) > 0; Euler: ψ(t) = √Q > 0; 10d: both roots).
# A log argument w of one sign there: log(-w) if negative (log(-w) = log w + const). Of both signs
# (a root inside, or different signs on different components of the domain): c log w =
# (c/2) log(w²) = c log|w|. A QuadLog log((U + √d V)/(U - √d V)) with U² - dV² < 0 there: the
# ratio is negative, use log((dV + √d U)/(dV - √d U)) (as in TE).
function real_logs_on(res::RationalIntegral{Q}, pos)
    logs = Tuple{Q,UPoly{Q}}[]
    for (c, w) in res.logs
        S = signs_on(pos, w)
        push!(logs, S ⊆ Set([1]) ? (c, w) : S == Set([-1]) ? (c, -w) : (c / 2, w * w))
    end
    quads = Any[]
    for q in res.quads
        if q isa QuadLog
            S = signs_on(pos, q.U * q.U - scale(Q(q.d), q.V * q.V))   # the sign of the ratio
            q = S == Set([-1]) ? QuadLog(q.β, q.d, scale(Q(q.d), q.V), q.U) :
                length(S) > 1 ? QuadLog(q.β, q.d, q.U, q.V, true) : q
        end
        push!(quads, q)
    end
    RationalIntegral(res.rational, logs, res.atans, res.unresolved, quads)
end

# f free of θᵢ (degree 0 over Kᵢ₋₁), repeatedly, as an element of the lowest level
function level_down(T::Tower, f)
    while levelof(T, f) > 0 && degree(f.num) == 0 && degree(f.den) == 0
        f = f.num.c[1] / f.den.c[1]
    end
    f
end

# step TL: the same for a tower integral over ℚ(t): the logs with a level-0 argument w ∈ ℚ(t)
# (sign of w = sign of num·den), and TowerQuadLogs with U, V ∈ ℚ(t) (as QuadLog). Arguments in θ
# (log(exp(t) - 2)) are kept.
function real_logs_tower(T::Tower, res::ElemIntegral{Q}, pos)
    logs = Tuple{Q,Any}[]
    for (c, w) in res.logs
        w = level_down(T, w)
        if levelof(T, w) == 0
            S = signs_on(pos, w.num * w.den)
            push!(logs, S ⊆ Set([1]) ? (c, w) : S == Set([-1]) ? (c, -w) : (c / 2, w * w))
        else
            push!(logs, (c, w))
        end
    end
    quads = Any[]
    for q in res.quads
        if q isa TowerQuadLog
            U, V = level_down(T, q.U), level_down(T, q.V)
            if levelof(T, U) == 0 && levelof(T, V) == 0
                w = U * U - frac(UPoly{Q}(Q[q.d])) * V * V      # the sign of the ratio
                S = signs_on(pos, w.num * w.den)
                q = S == Set([-1]) ? TowerQuadLog(q.β, q.d, frac(UPoly{Q}(Q[q.d])) * V, U) :
                    length(S) > 1 ? TowerQuadLog(q.β, q.d, U, V, true) : TowerQuadLog(q.β, q.d, U, V)
            end
        end
        push!(quads, q)
    end
    ElemIntegral(res.v, logs, res.atans, quads)
end

# step EC: the positivity constraints of a substitution as real elements (ℚ(i)(√d) ↦ ℚ(√d)), or
# nothing when a coefficient is not real
function real_pos(pos)
    out = Any[]
    for φ in pos
        r = real_frac(φ)
        r === nothing && return nothing
        push!(out, r)
    end
    out
end
real_coeff(c::Q) = c
real_coeff(c::QI) = iszero(c.im) ? c.re : nothing
function real_coeff(c::QSB{d,QI}) where {d}
    (iszero(c.a.im) && iszero(c.b.im)) || return nothing
    QS{d}(c.a.re, c.b.re)
end
real_coeff(c) = nothing
function real_poly(p::UPoly)
    cs = Any[real_coeff(c) for c in p.c]
    any(isnothing, cs) && return nothing
    isempty(cs) && return nothing
    R = typeof(cs[1])
    all(c -> c isa R, cs) || return nothing
    UPoly{R}(R[cs...])
end
real_frac(φ::Frac) = (n = real_poly(φ.num); d = real_poly(φ.den);
    (n === nothing || d === nothing || typeof(n) != typeof(d)) ? nothing : frac(n, d))
# R-polynomial as one over R2 (ℚ ⊂ ℚ(√d))
lift_poly(p::UPoly{Q}, ::Type{QS{d}}) where {d} = UPoly{QS{d}}(QS{d}[QS{d}(c, Q(0)) for c in p.c])
lift_poly(p::UPoly{R}, ::Type{R}) where {R} = p

# step EC: log pieces (c, :log, a) at the base of a real form (Step 7): a real argument a with one
# sign where all of pos are positive: log(-a) if negative; both signs: (c/2) log(a²)
function real_log_signs(T::Tower, pieces, pos)
    R = typeof(pos[1].num).parameters[1]
    C = ctype(T)
    out = Any[]
    for pc in pieces
        if pc[2] === :log && length(pc) == 3 && levelof(T, level_down(T, pc[3])) == 0
            a = level_down(T, pc[3])
            w = real_poly(a.num * a.den)
            w === nothing && (push!(out, pc); continue)
            w isa UPoly{R} || (w = try lift_poly(w, R) catch; nothing end)
            w === nothing && (push!(out, pc); continue)
            S = signs_on(pos, w)
            if S == Set([-1])
                push!(out, (pc[1], :log, -a))
            elseif length(S) > 1
                push!(out, (pc[1] * inv(cfromQ(C, Q(2))), :log, a * a))
            else
                push!(out, pc)
            end
        else
            push!(out, pc)
        end
    end
    out
end
