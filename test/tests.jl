using StaticArrays

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
    ctx = SG.polynomialctx(SG.Nmod32Γ(char), order=SG.Grevlex(5))

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
