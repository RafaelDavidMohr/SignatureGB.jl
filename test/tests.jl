using StaticArrays
using AbstractTrees
using DataStructures

function is_gb(pols::Vector{MP}) where {MP <: Singular.MPolyElem}
    id = Singular.Ideal(parent(first(pols)), pols)
    id.isGB = true
    gb_id = std(id)
    all(p -> iszero(Singular.reduce(p, id)), Singular.gens(gb_id))
end

function small_example()
    R, (x, y) = Singular.PolynomialRing(Singular.Fp(101), ["x", "y"])
    I = [x^2, x*y + y^2]
    order = SG.Grevlex(2)
    dat = SG.f5data(I, order=order)
    ctx = dat.ctx
    basis = SG.new_basis(ctx, 2)
    syz = SG.new_syz(ctx, 2)
    for i in 1:2
        SG.new_basis_elem!(ctx, basis, (SG.pos_type(ctx)(i), ctx.po.mo(R(1))))
    end
    R, (x, y), ctx, basis, syz
end

function cyclic(vars)
    n = length(vars)
    pols = [sum(prod(vars[j%n+1] for j in k:k+i) for k in 1:n) for i in 0:n-2]
    push!(pols, prod(vars[i] for i in 1:n)-1)
    return pols
end

@testset "sliceddict" begin
    ind = [(1, "a"), (2, "b")]
    vs = [1.0, 2.0]
    S = SG.SlicedDict(ind, vs)

    @test S[(1, "a")] == 1.0
    S[(2, "b")] = 3.0
    @test S[(2, "b")] == 3.0
    T = copy(S)
    Base.insert!(S, (3, "c"), 4.0)
    @test S[(3, "c")] == 4.0
    Base.delete!(S, (3, "c"))
    @test T == S

    ind = SG.SlicedInd(ind)
    view(ind, SG.SlicedInd([(2, "b")]))
    @test length(ind) == 2
    T = copy(ind)
    insert!(ind, (3, "c"))
    delete!(ind, (3, "c"))
    @test T == ind
end

@testset "termorder" begin
    order = SG.Grevlex(5)
    v = @SVector [2,2,3,4,5]
    w = @SVector [3,1,2,5,5]

    @test SG.lt(order, w, v)
    @test SG.iscompatible(order, v, w)
    @test !(SG.divides(order, v, w))
end

# stolen from pierre
@testset "polynomials" begin
    char = 4294967291
    ctx = SG.polynomialctx(SG.Nmod32Γ(char), monomials = SG.monomialctx(order=SG.Grevlex(5)))

    # Conversion from and to AA
    R, x = SG.abstractalgebra(ctx)

    p1 = (1+x[1]+x[2]+x[3])^10
    p0 = ctx(p1)

    @test R(ctx, p0) == p1
    @test SG.monomial(p0, 1) == ctx.mo(x[1]^10)
    @test length(p0) == binomial(10+3,3)

    # LCM
    @test SG.lcm(ctx.mo, ctx.mo([1,0,0,2,0]), ctx.mo([0,1,0,0,0])) == ctx.mo([1,1,0,2,0])

    # Shift
    @test R(ctx, SG.shift(ctx, p0, ctx.mo(x[1]^12*x[2]^6*x[3]))) == p1*x[1]^2*x[2]^6*x[3]
end

@testset "sig polynomials" begin
    R, (x, y) = Singular.PolynomialRing(Singular.Fp(101), ["x", "y"])
    f, g = x + y, x^2 + x*y + y^2
    
    order = SG.Grevlex(2)
    char = 101
    ctx = SG.idxsigpolynomialctx(SG.Nmod32Γ(char), 2, order=order)
    
    sig1, sig2 = ctx(1, R(1)), ctx(2, R(1))
    ctx(sig1, f), ctx(sig2, g)
    m1 = ctx.po.mo(x)
    @test collect(keys(ctx.tbl)) == [sig1, sig2]
    @test R(ctx.po, ctx(sig1)[:poly]) == f
    @test R(ctx.po, ctx(m1, sig1)[:poly]) == x*f
end

@testset "kd tree" begin
    R, (x, y) = Singular.PolynomialRing(Singular.Fp(101), ["x", "y"])
    f, g = x + y, y^3 + x*y + y^2
    
    order = SG.Grevlex(2)
    char = 101
    ctx = SG.idxsigpolynomialctx(SG.Nmod32Γ(char), 2, order=order)
    
    sig1, sig2 = ctx(1, R(1)), ctx(2, R(1))
    ctx(sig1, f), ctx(sig2, g)
    mo1, mo2 = ctx.po.mo(x), ctx.po.mo(y^3)
    kd_tree = SG.Kd_node([mo1, mo2], SG.pos_type(ctx))
    SG.insert_new_basis_element!(ctx, kd_tree, sig1)
    SG.insert_new_basis_element!(ctx, kd_tree, sig2)
    @test SG.div_query(ctx, kd_tree, mo1) == SG.SlicedInd([sig1])
    @test SG.div_query(ctx, kd_tree, mo2) == SG.SlicedInd([sig2])
end

@testset "f5 data" begin
    R, (x, y) = Singular.PolynomialRing(Singular.Fp(101), ["x", "y"])
    I = [x^2, y^2 + x*y]
    order = SG.Grevlex(2)
    dat = SG.f5data(I, order=order)
    sig1, sig2 = dat.ctx(1, R(1)), dat.ctx(2, R(1))
    @test SG.lt(dat.ctx, sig1, sig2)
end

@testset "pairs" begin
    R, (x, y), ctx, basis, syz = small_example()
    new_sig = ctx(2, x)
    ctx(new_sig, y^3)
    pairset = SG.pairset(ctx)
    SG.pairs!(ctx, pairset, new_sig, ctx.po.mo(y^3), basis, syz)
    @test isempty(pairset)
end

@testset "symbolic-pp" begin
    R, (x, y), ctx, basis, syz = small_example()
    pair_sig = (ctx.po.mo(x), ctx(2, R(1)))
    pair_sig_2 = (ctx.po.mo(y), ctx(1, R(1)))
    pairset = SG.mpairset(ctx, [pair_sig, pair_sig_2])
    SG.symbolic_pp!(ctx, pairset, basis, syz)
    test_sig_1 = (ctx.po.mo(y), ctx(1, R(1)))
    test_sig_2 = (ctx.po.mo(y), ctx(2, R(1)))
    test_pairset = SG.mpairset(ctx, [pair_sig, test_sig_1, test_sig_2])
    @test pairset == test_pairset
end

@testset "small-reduction" begin
    R, (x, y), ctx, basis, syz = small_example()
    pair_sig = (ctx.po.mo(x), ctx(2, R(1)))
    pairset = SG.mpairset(ctx)
    push!(pairset, pair_sig)
    mons = SG.symbolic_pp!(ctx, pairset, basis, syz, are_pairs = false)
    mat = SG.f5matrix(ctx, mons, pairset)
    @test SG.mat_show(mat) == [1 0 0; 0 1 1; 1 1 0]
    SG.reduction!(mat, ctx, trace_sig_tails = true)
    @test SG.mat_show(mat) == [1 0 0; 0 1 1; 0 0 100]
    p = SG.unindexpolynomial(mat.sigtail_mat.tbl,
                             mat.sigtail_mat.rows[last(mat.sigs)])
    @test R(ctx.po, p) == x - y
end
    
@testset "monomial hashing" begin
    order = SG.Grevlex(5)
    ctx = SG.monomialctx(exponents = Int64, order=SG.Grevlex(5))
    idx = SG.ixmonomialctx(ctx)

    v = @SVector [2,2,3,4,5]
    w = @SVector [3,1,2,5,5]

    m = SG.Monomial(v)
    n = SG.Monomial(w)
    i, j  = idx(m), idx(n)
    k = SG.mul(idx, i, j)
    @test SG.divides(idx, i, k)
    @test SG.divides(idx, j, k)
end

@testset "small groebner" begin
    R, (x, y) = Singular.PolynomialRing(Singular.Fp(101), ["x", "y"])
    I = [x^2, x*y + y^2]
    dat, G, H, pairs = SG.f5setup(I)
    SG.f5core!(dat, G, H, pairs)
    gb = vcat(I, [-y^3])
    gb_2 = [R(dat.ctx, (i, g[1])) for i in keys(G) for g in G[i]]
    @test all(p -> p in gb, gb_2)
end

@testset "small groebner 2" begin
    R, (x, y, z, t) = Singular.PolynomialRing(Singular.Fp(7), ["x", "y", "z", "t"])
    I = [y*z - 2*t^2, x*y + t^2, x^2*z + 3*x*t^2 - 2*y*t^2]
    dat, G, H, pairs = SG.f5setup(I)
    SG.f5core!(dat, G, H, pairs)
    gb = [R(dat.ctx, (i, g[1])) for i in keys(G) for g in G[i]]
    @test length(gb) == 7
end

@testset "cyclic 4" begin
    R, (x, y, z, w) = Singular.PolynomialRing(Singular.Fp(101), ["x", "y", "z", "w"])
    I = cyclic([x,y,z,w])
    dat, G, H, pairs = SG.f5setup(I)
    SG.f5core!(dat, G, H, pairs, verbose = true)
    gb = [R(dat.ctx, (i, g[1])) for i in keys(G) for g in G[i]]
    @test is_gb(gb)
end

@testset "cyclic 4 sigtails" begin
    R, (x, y, z, w) = Singular.PolynomialRing(Singular.Fp(101), ["x", "y", "z", "w"])
    I = cyclic([x,y,z,w])
    dat, G, H, pairs = SG.f5setup(I, trace_sig_tails = true)
    SG.f5core!(dat, G, H, pairs)
    basis_sigs = [(i, g[1]) for i in keys(G) for g in G[i]]
    gb = [R(dat.ctx, s) for s in basis_sigs]
    projs = [R(dat.ctx.po, SG.project(dat.ctx, s)) for s in basis_sigs]
    gb_s = [std(Ideal(R, I[1:k])) for k in 1:3]
    for (p, g, sig) in zip(projs, gb, basis_sigs)
        isone(sig[1]) && continue
        k = sig[1]
        @test iszero(Singular.reduce(p*I[k] - g, gb_s[k - 1]))
    end
end

@testset "cyclic 6" begin
    R, (x1, x2, x3, x4, x5, x6) = Singular.PolynomialRing(Singular.Fp(101), ["x$(i)" for i in 1:6])
    I = cyclic([x1,x2,x3,x4,x5,x6])
    dat, G, H, pairs = SG.f5setup(I)
    times = SG.f5core!(dat, G, H, pairs)
    gb = [R(dat.ctx, (i, g[1])) for i in keys(G) for g in G[i]]
    @test is_gb(gb)
end
