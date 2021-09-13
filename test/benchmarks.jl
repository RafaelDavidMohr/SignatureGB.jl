using BenchmarkTools
using SignatureGB
using Combinatorics

SG = SignatureGB

function divmask_benchmark(nvars, nmons)
    suite = BenchmarkGroup()

    suite["monomials"] = BenchmarkGroup()

    order = SG.Grevlex(nvars)
    ctx = SG.monomialctx(exponents = Int64, order=order)
    idx = SG.ixmonomialctx(ctx)
    
    mons = [SG.Monomial(rand(1:100, SVector{nvars, Int64})) for i in 1:nmons]
    idx_mons = [idx(m) for m in mons]

    suite["monomials"]["mask_hitting"] = @benchmarkable [idx.table.bitmasks[ts[1]] & (~ idx.table.bitmasks[ts[2]]) for ts in $(combinations(idx_mons, 2))]
    suite["monomials"]["divis_with_mask"] = @benchmarkable [SG.divides(idx, ts[1], ts[2]) for ts in $(combinations(idx_mons, 2))]
    suite["monomials"]["naive_divis"] = @benchmarkable [SG.divides(ctx, ts[1], ts[2]) for ts in $(combinations(mons, 2))]
    tune!(suite)
    suite
end

