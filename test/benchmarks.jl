using BenchmarkTools
using SignatureGB
using Combinatorics
using Dictionaries

SG = SignatureGB

function divmask_benchmark(nvars, nmons)
    suite = BenchmarkGroup()

    suite["monomials"] = BenchmarkGroup()

    order = SG.Grevlex(nvars)
    ctx = SG.monomialctx(exponents = Int64, order=order)
    idx = SG.ixmonomialctx(ctx)

    mons = [SG.Monomial(rand(1:100, SVector{nvars, Int})) for i in 1:nmons]
    idx_mons = [idx(m) for m in mons]
    itr = combinations(idx_mons, 2)

    suite["monomials"]["divis_with_mask"] = @benchmarkable [SG.divides(idx, ts[1], ts[2]) for ts in $(itr)]
    suite["monomials"]["naive_divis"] = @benchmarkable [SG.divides(ctx, idx.table[ts[1]], idx.table[ts[2]]) for ts in $(itr)]
    suite, idx, ctx, mons
end

function sliceddict_benchmark()
    suite = BenchmarkGroup()
    alph = ["a", "b", "c", "d", "e", "f", "g", "h"]
    rng = 1:100000
    keys = [(lett, i) for lett in alph for i in rng]
    dct_1 = Dictionary(keys, keys)
    dct_2 = SG.SlicedDict(keys, keys)
    suite["plain_dict"] = @benchmarkable getindices($(dct_1), filter(a -> a[1] == "a", keys($(dct_1))))
    suite["sliced_dict"] = @benchmarkable $(dct_2)["a"]
    suite, dct_1, dct_2
end
