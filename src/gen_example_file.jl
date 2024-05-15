using Singular

function is_gb(pols::Vector{MP}) where {MP <: Singular.MPolyRingElem}
    id = Singular.Ideal(parent(first(pols)), pols)
    id.isGB = true
    gb_id = std(id)
    all(p -> iszero(Singular.reduce(p, id)), Singular.gens(gb_id))
end

function cyclic(vars)
    n = length(vars)
    pols = [sum(prod(vars[j%n+1] for j in k:k+i) for k in 1:n) for i in 0:n-2]
    push!(pols, prod(vars[i] for i in 1:n)-1)
    return pols
end
