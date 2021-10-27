using StaticArrays
using AbstractTrees
using DataStructures

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
    rows = sort(collect(pairset), lt = (a, b) -> Base.Order.lt(SG.mpairordering(ctx), a, b))
    mat = SG.f5matrix(ctx, mons, rows)
    @test SG.mat_show(mat) == [1 0 0; 0 1 1; 1 1 0]
    SG.reduction!(mat)
    @test SG.mat_show(mat) == [1 0 0; 0 1 1; 0 0 1]
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
    gb_2 = SG.f5(I, interreduction = false)
    gb = vcat(I, [y^3])
    @test all(p -> p in gb, gb_2)
end

@testset "small groebner 2" begin
    R, (x, y, z, t) = Singular.PolynomialRing(Singular.Fp(7), ["x", "y", "z", "t"])
    I = [y*z - 2*t^2, x*y + t^2, x^2*z + 3*x*t^2 - 2*y*t^2]
    gb = SG.f5(I, interreduction = false)
    @test length(gb) == 7
end

@testset "cyclic 4" begin
    R, (x, y, z, w) = Singular.PolynomialRing(Singular.Fp(101), ["x", "y", "z", "w"])
    I = SG.cyclic([x,y,z,w])
    gb = SG.f5(I, interreduction = false)
    @test SG.is_gb(gb)
end

@testset "cyclic 6" begin
    R, (x1, x2, x3, x4, x5, x6) = Singular.PolynomialRing(Singular.Fp(101), ["x$(i)" for i in 1:6])
    I = SG.cyclic([x1,x2,x3,x4,x5,x6])
    gb = SG.f5(I, interreduction = false)
    @test SG.is_gb(gb)
end

@testset "katsura 6 interreduction" begin
    R, (x1, x2, x3, x4, x5, x6) = Singular.PolynomialRing(Singular.Fp(65521), ["x$(i)" for i in 1:6])
    I = [x1+2*x2+2*x3+2*x4+2*x5+2*x6-1,
         x1^2+2*x2^2+2*x3^2+2*x4^2+2*x5^2+2*x6^2-x1,
         2*x1*x2+2*x2*x3+2*x3*x4+2*x4*x5+2*x5*x6-x2,
         x2^2+2*x1*x3+2*x2*x4+2*x3*x5+2*x4*x6-x3,
         2*x2*x3+2*x1*x4+2*x2*x5+2*x3*x6-x4,
         x3^2+2*x2*x4+2*x1*x5+2*x2*x6-x5]
    gb = SG.f5(I)
    @test length(gb) == 22
end
