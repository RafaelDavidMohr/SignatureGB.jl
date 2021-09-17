using BenchmarkTools
using SignatureGB
using Combinatorics
using Dictionaries
using Oscar

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

function kd_tree_benchmark(npols, nmons)
    suite = BenchmarkGroup()
    R, vars = PolynomialRing(GF(101), ["x$(i)" for i in 1:32], ordering = :degrevlex)
    order = SG.Grevlex(32)
    char = 101
    ctx = SG.idxsigpolynomialctx(SG.Nmod32Γ(char), order = order)
    pols = filter(p -> !(iszero(p)), [rand(R, 1:1, 1:10) for _ in 1:npols])
    sigs = [ctx(i, R(1)) for i in eachindex(pols)]
    for (p, s) in zip(pols, sigs)
        ctx(s, p)
    end
    exp_type = SG.exponenttype(ctx.po.mo)
    exps = exp_type[collect(1:10)...]
    kd_mons = [ctx.po.mo(SG.Monomial(SVector{32, exp_type}([j == i ? rand(exps) : zero(exp_type) for j in 1:32])))
               for i in [rand(1:32) for _ in 1:16]]
    kd_tree = SG.Kd_node(kd_mons, SG.pos_type(ctx))
    [SG.insert_new_basis_element!(ctx, kd_tree, s) for s in sigs]
    mons = [ctx.po.mo(SG.Monomial(rand(1:10, SVector{32, exp_type}))) for _ in 1:nmons]

    suite["div_query_kd_tree"] = @benchmarkable [SG.div_query($(ctx), $(kd_tree), m) for m in $(mons)]
    suite["div_query"] = @benchmarkable [filter(be -> SG.divides($(ctx).po.mo, SG.leadingmonomial($(ctx), be), m),
                                                $(sigs)) for m in $(mons)]
    suite, ctx, kd_tree, mons, sigs
end
