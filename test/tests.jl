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

function contained_in(I1::sideal{MP},
                      I2::sideal{MP}) where {MP <: Singular.MPolyElem}

    gb = std(I2)
    all(p -> iszero(reduce(p, gb)), gens(I1))
end

function is_eq(I1::sideal{MP},
               I2::sideal{MP}) where {MP <: Singular.MPolyElem}

    contained_in(I1, I2) && contained_in(I2, I1)
end

function fancy_loop(I::Vector{MP};
                    interreduce = false) where {MP <: Singular.MPolyElem}

    R = parent(first(I))
    I_prime = Ideal(R, first(I))
    Js = typeof(I_prime)[]
    for f in I[2:end]
        f_id = Ideal(R, f)
        I_sat = saturation(I_prime, f_id)[1]
        if !(is_eq(I_prime, I_sat))
            push!(Js, saturation(I_prime, I_sat)[1])
        end
        I_prime = I_sat + f_id
    end

    for J in Js
        I_prime = saturation(I_prime, J)[1]
    end
    interreduce ? std(I_prime, complete_reduction = true) : I_prime
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
    char = 65521
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
    two = SG.pos_type(ctx)(2)
    mons = SG.symbolic_pp!(ctx, pairset, basis, syz, are_pairs = false)
    rows = sort(collect(pairset), lt = (a, b) -> Base.Order.lt(SG.mpairordering(ctx), a, b))
    mat = SG.f5matrix(ctx, mons, rows, two, two, :f, trace_sig_tail_tags = [:f, :g])
    @test SG.mat_show(mat) == [1 0 0; 0 1 1; 1 1 0]
    SG.reduction!(mat)
    @test SG.mat_show(mat) == [1 0 0; 0 1 1; 0 0 100]
    p = SG.unindexpolynomial(mat.sigtail_mat.tbl,
                             mat.sigtail_mat.rows[pair_sig])
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
    gb_2 = SG.f5(I, interreduction = false)
    gb = vcat(I, [-y^3])
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
    gb = SG.f5(I, interreduction = false, verbose = 1)
    @test SG.is_gb(gb)
end

@testset "cyclic 4 sigtails" begin
    R, (x, y, z, w) = Singular.PolynomialRing(Singular.Fp(101), ["x", "y", "z", "w"])
    I = SG.cyclic([x,y,z,w])
    dat = SG.f5setup(I, trace_sig_tail_tags = [:f, :g])
    G, H, pairs = SG.pairs_and_basis(dat, length(I))
    SG.f5core!(dat, G, H, pairs, interreduction = false)
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

@testset "cyclic 6 sigtails" begin
    R, (x1, x2, x3, x4, x5, x6) = Singular.PolynomialRing(Singular.Fp(101), ["x$(i)" for i in 1:6])
    I = SG.cyclic([x1,x2,x3,x4,x5,x6])
    dat = SG.f5setup(I, trace_sig_tail_tags = [:f, :g])
    G, H, pairs = SG.pairs_and_basis(dat, length(I))
    SG.f5core!(dat, G, H, pairs, interreduction = false)
    basis_sigs = [(i, g[1]) for i in keys(G) for g in G[i]]
    gb = [R(dat.ctx, s) for s in basis_sigs]
    projs = [R(dat.ctx.po, SG.project(dat.ctx, s)) for s in basis_sigs]
    gb_s = [std(Ideal(R, I[1:k])) for k in 1:5]
    for (p, g, sig) in zip(projs, gb, basis_sigs)
        isone(sig[1]) && continue
        k = sig[1]
        @test iszero(Singular.reduce(p*I[k] - g, gb_s[k - 1]))
    end
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

@testset "small-decomp" begin
    R, (x, y, z) = Singular.PolynomialRing(Singular.Fp(101), ["x", "y", "z"])
    I = [x*y, x*z]
    gb = decompose(I, interreduction = false)
    @test SG.is_gb(gb)
    @test is_eq(Ideal(R, gb), fancy_loop(I))
end

@testset "cyclic 4 decomp" begin
    R, (x, y, z, w) = Singular.PolynomialRing(Singular.Fp(101), ["x", "y", "z", "w"])
    I = SG.cyclic([x,y,z,w])
    gb = decompose(I, interreduction = false)
    @test SG.is_gb(gb)
    @test is_eq(Ideal(R, gb), fancy_loop(I))
end

@testset "cyclic 6 decomp" begin
    R, (x1, x2, x3, x4, x5, x6) = Singular.PolynomialRing(Singular.Fp(101), ["x$(i)" for i in 1:6])
    I = SG.cyclic([x1,x2,x3,x4,x5,x6])
    gb = decompose(I, interreduction = false)
    @test SG.is_gb(gb)
    @test is_eq(Ideal(R, gb), fancy_loop(I))
end

@testset "singhypcritpoints decomp" begin
    R, (x1, x2, x3, x4)  = Singular.PolynomialRing(Singular.Fp(65521), ["x1", "x2", "x3", "x4"])
    I = [2297232*x1^4+10816588*x1^3*x2-19696652*x1^3*x3+12014836*x1^3*x4+19038581*x1^2*x2^2+25140479*x1^2*x2*x3-124056256*x1^2*x2*x4-19352961*x1^2*x3^2+30086207*x1^2*x3*x4-15861565*x1^2*x4^2-64545276*x1*x2^3-3395230*x1*x2^2*x3+125153935*x1*x2^2*x4-10319588*x1*x2*x3^2+5839912*x1*x2*x3*x4+112915639*x1*x2*x4^2+12114032*x1*x3^3+32314614*x1*x3^2*x4-5646418*x1*x3*x4^2-3823868*x1*x4^3+40572828*x2^4-42051502*x2^3*x3-17361686*x2^3*x4+66618627*x2^2*x3^2-61020343*x2^2*x3*x4-66491064*x2^2*x4^2+16298428*x2*x3^3+46623254*x2*x3^2*x4-26720875*x2*x3*x4^2-16047619*x2*x4^3+15073900*x3^4+9644976*x3^3*x4-9790086*x3^2*x4^2-9372130*x3*x4^3+4661500*x4^4-39813328*x1^3-9400295*x1^2*x2-1289811*x1^2*x3+64756487*x1^2*x4-41226416*x1*x2^2+22255617*x1*x2*x3+115474646*x1*x2*x4+54583668*x1*x3^2+150465505*x1*x3*x4-19224417*x1*x4^2+52554279*x2^3-1318549*x2^2*x3-91874169*x2^2*x4+119183502*x2*x3^2-131012023*x2*x3*x4-88321124*x2*x4^2+41605616*x3^3+58052114*x3^2*x4-70772721*x3*x4^2+3123219*x4^3+99968607*x1^2-17533608*x1*x2+133696391*x1*x3-71771275*x1*x4+20484256*x2^2+10206682*x2*x3-58141098*x2*x4+72704712*x3^2-111938286*x3*x4-5946966*x4^2-46338000*x1+12230767*x2-23665371*x3+7665457*x4+9313394, 10816588*x1^3+38077162*x1^2*x2+25140479*x1^2*x3-124056256*x1^2*x4-193635828*x1*x2^2-6790460*x1*x2*x3+250307870*x1*x2*x4-10319588*x1*x3^2+5839912*x1*x3*x4+112915639*x1*x4^2+162291312*x2^3-126154506*x2^2*x3-52085058*x2^2*x4+133237254*x2*x3^2-122040686*x2*x3*x4-132982128*x2*x4^2+16298428*x3^3+46623254*x3^2*x4-26720875*x3*x4^2-16047619*x4^3-9400295*x1^2-82452832*x1*x2+22255617*x1*x3+115474646*x1*x4+157662837*x2^2-2637098*x2*x3-183748338*x2*x4+119183502*x3^2-131012023*x3*x4-88321124*x4^2-17533608*x1+40968512*x2+10206682*x3-58141098*x4+12230767, -19696652*x1^3+25140479*x1^2*x2-38705922*x1^2*x3+30086207*x1^2*x4-3395230*x1*x2^2-20639176*x1*x2*x3+5839912*x1*x2*x4+36342096*x1*x3^2+64629228*x1*x3*x4-5646418*x1*x4^2-42051502*x2^3+133237254*x2^2*x3-61020343*x2^2*x4+48895284*x2*x3^2+93246508*x2*x3*x4-26720875*x2*x4^2+60295600*x3^3+28934928*x3^2*x4-19580172*x3*x4^2-9372130*x4^3-1289811*x1^2+22255617*x1*x2+109167336*x1*x3+150465505*x1*x4-1318549*x2^2+238367004*x2*x3-131012023*x2*x4+124816848*x3^2+116104228*x3*x4-70772721*x4^2+133696391*x1+10206682*x2+145409424*x3-111938286*x4-23665371, 12014836*x1^3-124056256*x1^2*x2+30086207*x1^2*x3-31723130*x1^2*x4+125153935*x1*x2^2+5839912*x1*x2*x3+225831278*x1*x2*x4+32314614*x1*x3^2-11292836*x1*x3*x4-11471604*x1*x4^2-17361686*x2^3-61020343*x2^2*x3-132982128*x2^2*x4+46623254*x2*x3^2-53441750*x2*x3*x4-48142857*x2*x4^2+9644976*x3^3-19580172*x3^2*x4-28116390*x3*x4^2+18646000*x4^3+64756487*x1^2+115474646*x1*x2+150465505*x1*x3-38448834*x1*x4-91874169*x2^2-131012023*x2*x3-176642248*x2*x4+58052114*x3^2-141545442*x3*x4+9369657*x4^2-71771275*x1-58141098*x2-111938286*x3-11893932*x4+7665457]
    gb = decompose(I, interreduction = false)
    @test SG.is_gb(gb)
    @test is_eq(Ideal(R, gb), fancy_loop(I))
    gb = decompose(I)
    @test SG.is_gb(gb)
    @test length(gb) == length(gens(fancy_loop(I, interreduce = true)))
end
