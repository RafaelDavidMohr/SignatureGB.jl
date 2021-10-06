using SignatureGB
using Singular

function cyclic(vars)
    n = length(vars)
    pols = [sum(prod(vars[j%n+1] for j in k:k+i) for k in 1:n) for i in 0:n-2]
    push!(pols, prod(vars[i] for i in 1:n)-1)
    return pols
end

function is_gb(pols::Vector{MP}) where {MP <: Singular.MPolyElem}
    id = Singular.Ideal(parent(first(pols)), pols)
    id.isGB = true
    gb_id = std(id)
    all(p -> iszero(Singular.reduce(p, id)), Singular.gens(gb_id))
end

function f5stats(pols::Vector{MP}) where {MP <: Singular.MPolyElem}
    dat, G, H, pairs = SignatureGB.f5setup(pols)
    times, stats = SignatureGB.f5core!(dat, G, H, pairs)
    pretty_print_stats(times, stats)
end

function pretty_print_stats(times, stats)
    "time spent for reduction: $(times.reduction)
time spent for rewrite checks during pair construction/symbolic pp: $(times.rewrite)
time spent for rewrite checks of pairs with new elements: $(times.new_rewriter)
number of matrices: $(length(stats.matrix_sizes))
rows x columns of matrices: $(stats.matrix_sizes)
position and degree of zero reductions: $(stats.zero_reductions)
total number of arithmetic operations: $(stats.arit_operations)"
end
