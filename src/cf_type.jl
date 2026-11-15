# CF{B}: ℚ(t₁, …, tₖ) as one type, the level a field (flat_constants.jl). The type alone, here, so that the files
# included before flat_constants.jl can dispatch on it
struct CF{B}
    lev::Int
    val::B
    f::Union{Nothing,Frac{UPoly{CF{B}}}}
end

const CFFrac{B} = Frac{UPoly{CF{B}}}
const TField = Union{Frac,CF}                   # (dispatch: a constant field with generators, either kind)
CF{B}(v::B) where {B} = CF{B}(0, v, nothing)
