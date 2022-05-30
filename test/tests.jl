using StaticArrays
using AbstractTrees
using DataStructures

function small_example(;kwargs...)
    R, (x, y) = Singular.PolynomialRing(Singular.Fp(101), ["x", "y"])
    I = [x^2, x*y + y^2]

    ctx = SG.setup(I; kwargs...)
    basis = SG.new_basis(ctx)
    syz = SG.new_syz(ctx)
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

# check probabilistically if the radical of I2 is contained in the radical of I1
function radical_contained_in(I1::sideal{MP},
                              I2::sideal{MP}) where {MP <: Singular.MPolyElem}

    R = base_ring(I1)
    f = sum([rand(1:characteristic(R))*g for g in gens(R)])
    tes = std(Singular.saturation(I1, Ideal(R, f))[1])
    iszero(reduce(R(1), tes))
end

function is_radical_eq(I1::sideal{MP},
                       I2::sideal{MP}) where {MP <: Singular.MPolyElem}

    radical_contained_in(I1, I2) && radical_contained_in(I2, I1)
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
    ctx = SG.polynomialctx(SG.Nmod32Γ(char), order = SG.Grevlex(5),indexed=false)

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

@testset "monomial hashing" begin
    order = SG.Grevlex(5)
    ctx = SG.monomialctx(exponents = Int64, order=SG.Grevlex(5), indexed = false)
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

@testset "sig polynomials" begin
    R, (x, y) = Singular.PolynomialRing(Singular.Fp(101), ["x", "y"])
    f, g = x + y, x^2 + x*y + y^2
    
    order = SG.Grevlex(2)
    char = 101
    ctx = SG.sigpolynomialctx(SG.Nmod32Γ(char), 2, order=order)
    
    sig1, sig2 = ctx(1, R(1)), ctx(2, R(1))
    ctx(sig1, f), ctx(sig2, g)
    m1 = ctx.po.mo(x)
    @test Set(collect(keys(ctx.tbl))) == Set([sig1, sig2])
    @test R(ctx.po, ctx(sig1).pol) == f
    @test R(ctx.po, ctx(m1, sig1).pol) == x*f
    @test SG.mod_order(ctx) == :POT
    @test SG.lt(ctx, sig1, sig2)
end

@testset "setup" begin
    R, (x, y) = Singular.PolynomialRing(Singular.Fp(101), ["x", "y"])
    I = [x + y, x^2 + x*y + y^2]

    ctx = SG.setup(I)
    @test SG.mod_order(ctx) == :POT
    @test SG.pos_type(ctx) == UInt16

    ctx = SG.setup(I, indexed = false, exponents = Int32)
    @test SG.exponenttype(ctx.po.mo) == Int32

    ctx = SG.setup(I, buffer = 128)
    @test typeof(ctx.po.co) <: SG.Nmod32xΓ

    ctx = SG.setup(I, mod_order = :SCHREY)
    @test SG.mod_order(ctx) == :SCHREY
end

@testset "pairs" begin
    R, (x, y), ctx, basis, syz = small_example()
    new_sig = ctx(2, x)
    koszul_syz = ctx(2, x^2)
    ctx(new_sig, y^3)
    koszul_q = SG.koszul_queue(ctx)
    push!(koszul_q, koszul_syz)
    pairset = SG.pairset(ctx)
    SG.pairs!(ctx, pairset, new_sig, ctx.po.mo(y^3), basis, syz, false)
    @test length(pairset) == 1
    @test SG.check!(koszul_q, first(pairset))
end

@testset "symbolic-pp" begin
    R, (x, y), ctx, basis, syz = small_example()
    pair_sig = (ctx.po.mo(x), ctx(2, R(1)))
    pair_sig_2 = (ctx.po.mo(y), ctx(1, R(1)))
    pairset = SG.mpairset(ctx, [pair_sig, pair_sig_2])
    tbl, module_tbl, sigpolys = SG.symbolic_pp!(ctx, pairset, basis, syz, false, 2)
    result_sigs = [first(tup) for tup in sigpolys]
    test_sig_2 = (ctx.po.mo(y), ctx(2, R(1)))
    test_sigs = [pair_sig, pair_sig_2, test_sig_2]
    @test all(sig -> sig in result_sigs, test_sigs) && all(sig -> sig in test_sigs, result_sigs)
end

@testset "small-reduction" begin
    R, (x, y), ctx, basis, syz = small_example()
    pair_sig = (ctx.po.mo(x), ctx(2, R(1)))
    pairset = SG.mpairset(ctx)
    push!(pairset, pair_sig)
    tbl, module_tbl, sigpolys = SG.symbolic_pp!(ctx, pairset, basis, syz, false, 2, are_pairs = false)
    mat = SG.f5_matrix(ctx, tbl, module_tbl, sigpolys)
    @test SG.mat_show(mat) == [1 0 0; 0 1 1; 1 1 0]
    SG.reduction!(mat)
    @test SG.mat_show(mat) == [1 0 0; 0 1 1; 0 0 1]
end

# @testset "small groebner" begin
#     R, (x, y) = Singular.PolynomialRing(Singular.Fp(101), ["x", "y"])
#     I = [x^2, x*y + y^2]
#     gb_2 = SG.sgb(I)
#     gb = vcat(I, [-y^3])
#     @test all(p -> p in gb, gb_2)
# end

# @testset "small groebner schreyer" begin
#     R, (x, y) = Singular.PolynomialRing(Singular.Fp(101), ["x", "y"])
#     I = [x^2, x*y + y^2]
#     gb_2 = SG.sgb(I, mod_order = :SCHREY)
#     gb = vcat(I, [-y^3])
#     @test all(p -> p in gb, gb_2)
# end

# @testset "module rep" begin
#     R, (x, y), ctx, basis, syz = small_example(mod_rep_type = :highest_index)
#     pair_sig = (ctx.po.mo(x), ctx(2, R(1)))
#     pairset = SG.mpairset(ctx)
#     push!(pairset, pair_sig)
#     mons = SG.symbolic_pp!(ctx, pairset, basis, syz, false, are_pairs = false)
#     mat = SG.F5matrixHighestIndex(ctx, mons, collect(pairset))
#     SG.reduction!(mat)
#     println(SG.mat_show(mat.module_matrix))
# end

# @testset "small groebner 2" begin
#     R, (x, y, z, t) = Singular.PolynomialRing(Singular.Fp(7), ["x", "y", "z", "t"])
#     I = [y*z - 2*t^2, x*y + t^2, x^2*z + 3*x*t^2 - 2*y*t^2]
#     gb = SG.sgb(I)
#     @test length(gb) == 7
# end

# @testset "cyclic 4" begin
#     R, (x, y, z, w) = Singular.PolynomialRing(Singular.Fp(101), ["x", "y", "z", "w"])
#     I = SG.cyclic([x,y,z,w])
#     gb = SG.sgb(I)
#     @test SG.is_gb(gb)
# end

# @testset "f45 sat" begin
#     R, (x0, x1, x2, x3, x4, x5, x6)  = Singular.PolynomialRing(Singular.Fp(65521), ["x0", "x1", "x2", "x3", "x4", "x5", "x6"])
#     J = SG.cyclic(gens(R)[1:6])
#     I = J[1:4]
#     f = J[5]
#     gb = SG.f45sat(I, f, verbose = 1)
#     gb_tes = saturation(Ideal(R, I), Ideal(R, f))[1]
#     @test is_eq(Ideal(R, gb), gb_tes)
#     F = [1605136*x1^4-17831620*x1^3*x2-4868992*x1^3*x3+1756936*x1^3*x4+105592*x1^3*x5+4599176*x1^3*x6+55184871*x1^2*x2^2+32263630*x1^2*x2*x3-8889852*x1^2*x2*x4-6656950*x1^2*x2*x5-30560941*x1^2*x2*x6+17360988*x1^2*x3^2+20982140*x1^2*x3*x4-7871668*x1^2*x3*x5-8728440*x1^2*x3*x6+8810524*x1^2*x4^2-1086052*x1^2*x4*x5+2367930*x1^2*x4*x6-838628*x1^2*x5^2+397478*x1^2*x5*x6+1301489*x1^2*x6^2-18794652*x1*x2^3-10507577*x1*x2^2*x3+1771815*x1*x2^2*x4+39833981*x1*x2^2*x5+26404066*x1*x2^2*x6+19142338*x1*x2*x3^2-27598109*x1*x2*x3*x4+78227493*x1*x2*x3*x5+4449587*x1*x2*x3*x6-23393030*x1*x2*x4^2+22974756*x1*x2*x4*x5-8575699*x1*x2*x4*x6-17431*x1*x2*x5^2-14220914*x1*x2*x5*x6+12626078*x1*x2*x6^2-7753088*x1*x3^3-19664812*x1*x3^2*x4+38196980*x1*x3^2*x5-19848532*x1*x3^2*x6+16452638*x1*x3*x4^2+8414788*x1*x3*x4*x5-4297868*x1*x3*x4*x6+14208110*x1*x3*x5^2+4398980*x1*x3*x5*x6+30984190*x1*x3*x6^2+20073712*x1*x4^3-15135504*x1*x4^2*x5+8127330*x1*x4^2*x6+17230458*x1*x4*x5^2+12786158*x1*x4*x5*x6+22857068*x1*x4*x6^2-2909938*x1*x5^3-4773782*x1*x5^2*x6-4467088*x1*x5*x6^2-6110768*x1*x6^3-51658273*x2^4-13274261*x2^3*x3+47461556*x2^3*x4-23925350*x2^3*x5+45796446*x2^3*x6+25794921*x2^2*x3^2-1241027*x2^2*x3*x4+22323446*x2^2*x3*x5+17849505*x2^2*x3*x6+13012721*x2^2*x4^2-36311783*x2^2*x4*x5-5343255*x2^2*x4*x6+51615626*x2^2*x5^2+38958894*x2^2*x5*x6-32052865*x2^2*x6^2-5155556*x2*x3^3+1110700*x2*x3^2*x4+19812362*x2*x3^2*x5-30924318*x2*x3^2*x6+35608159*x2*x3*x4^2-76548845*x2*x3*x4*x5+32445937*x2*x3*x4*x6+83606730*x2*x3*x5^2-1740302*x2*x3*x5*x6+16796826*x2*x3*x6^2-35141286*x2*x4^3+60785734*x2*x4^2*x5-14359008*x2*x4^2*x6-58463497*x2*x4*x5^2-16405034*x2*x4*x5*x6-41541916*x2*x4*x6^2+34359864*x2*x5^3+22061298*x2*x5^2*x6+42286600*x2*x5*x6^2+17904528*x2*x6^3+962948*x3^4+3561908*x3^3*x4-8776964*x3^3*x5+4948020*x3^3*x6-3911247*x3^2*x4^2-11571902*x3^2*x4*x5+7433906*x3^2*x4*x6+17058245*x3^2*x5^2-29151714*x3^2*x5*x6+2898881*x3^2*x6^2-11640806*x3*x4^3+37992804*x3*x4^2*x5-25116626*x3*x4^2*x6-30041260*x3*x4*x5^2+19176418*x3*x4*x5*x6-22397228*x3*x4*x6^2+23473998*x3*x5^3-1940970*x3*x5^2*x6+22261360*x3*x5*x6^2-20505680*x3*x6^3+11464876*x4^4-14585780*x4^3*x5+11351580*x4^3*x6+22084514*x4^2*x5^2+4510732*x4^2*x5*x6+28352924*x4^2*x6^2-11350358*x4*x5^3+1832444*x4*x5^2*x6-9174464*x4*x5*x6^2+11962528*x4*x6^3+6339025*x5^4+7057752*x5^3*x6+20200136*x5^2*x6^2+11169728*x5*x6^3+11715008*x6^4-4051328*x1^3+24401362*x1^2*x2-1564496*x1^2*x3-8230572*x1^2*x4-2278084*x1^2*x5-6750768*x1^2*x6-21618288*x1*x2^2+7898523*x1*x2*x3+16022151*x1*x2*x4+19860298*x1*x2*x5+19551604*x1*x2*x6+24423072*x1*x3^2+9663290*x1*x3*x4+25225782*x1*x3*x5-8258422*x1*x3*x6-10191758*x1*x4^2+19893514*x1*x4*x5-16449358*x1*x4*x6-6868780*x1*x5^2-8435036*x1*x5*x6-3966056*x1*x6^2-12101458*x2^3-32470992*x2^2*x3+20793594*x2^2*x4-25646562*x2^2*x5-16187207*x2^2*x6+23751426*x2*x3^2-11042785*x2*x3*x4+49926780*x2*x3*x5+6676334*x2*x3*x6+3791551*x2*x4^2-30363266*x2*x4*x5+30015366*x2*x4*x6+52561304*x2*x5^2+8443456*x2*x5*x6-3184536*x2*x6^2-5561108*x3^3-6937814*x3^2*x4+20576418*x3^2*x5-17036298*x3^2*x6+20956048*x3*x4^2-31149992*x3*x4*x5+16685258*x3*x4*x6+49921018*x3*x5^2-17459028*x3*x5*x6+27548600*x3*x6^2-6200850*x4^3+26401098*x4^2*x5-12818056*x4^2*x6-21504014*x4*x5^2+8604776*x4*x5*x6-14934304*x4*x6^2+18535580*x5^3+4354764*x5^2*x6+20574752*x5*x6^2-6498944*x6^3+351892*x1^2+15869383*x1*x2+33018752*x1*x3+27159978*x1*x4-5578786*x1*x5-1478078*x1*x6-1163014*x2^2+15770498*x2*x3-42544231*x2*x4+47610560*x2*x5-4542562*x2*x6+598421*x3^2-15967864*x3*x4+58917022*x3*x5-29932266*x3*x6+29104703*x4^2-22705154*x4*x5+20325284*x4*x6+35264562*x5^2+6837024*x5*x6+33343808*x6^2-2626464*x1-2523880*x2+23751226*x3-7763622*x4+29927948*x5-10650840*x6+17646289, -17831620*x1^3+110369742*x1^2*x2+32263630*x1^2*x3-8889852*x1^2*x4-6656950*x1^2*x5-30560941*x1^2*x6-56383956*x1*x2^2-21015154*x1*x2*x3+3543630*x1*x2*x4+79667962*x1*x2*x5+52808132*x1*x2*x6+19142338*x1*x3^2-27598109*x1*x3*x4+78227493*x1*x3*x5+4449587*x1*x3*x6-23393030*x1*x4^2+22974756*x1*x4*x5-8575699*x1*x4*x6-17431*x1*x5^2-14220914*x1*x5*x6+12626078*x1*x6^2-206633092*x2^3-39822783*x2^2*x3+142384668*x2^2*x4-71776050*x2^2*x5+137389338*x2^2*x6+51589842*x2*x3^2-2482054*x2*x3*x4+44646892*x2*x3*x5+35699010*x2*x3*x6+26025442*x2*x4^2-72623566*x2*x4*x5-10686510*x2*x4*x6+103231252*x2*x5^2+77917788*x2*x5*x6-64105730*x2*x6^2-5155556*x3^3+1110700*x3^2*x4+19812362*x3^2*x5-30924318*x3^2*x6+35608159*x3*x4^2-76548845*x3*x4*x5+32445937*x3*x4*x6+83606730*x3*x5^2-1740302*x3*x5*x6+16796826*x3*x6^2-35141286*x4^3+60785734*x4^2*x5-14359008*x4^2*x6-58463497*x4*x5^2-16405034*x4*x5*x6-41541916*x4*x6^2+34359864*x5^3+22061298*x5^2*x6+42286600*x5*x6^2+17904528*x6^3+24401362*x1^2-43236576*x1*x2+7898523*x1*x3+16022151*x1*x4+19860298*x1*x5+19551604*x1*x6-36304374*x2^2-64941984*x2*x3+41587188*x2*x4-51293124*x2*x5-32374414*x2*x6+23751426*x3^2-11042785*x3*x4+49926780*x3*x5+6676334*x3*x6+3791551*x4^2-30363266*x4*x5+30015366*x4*x6+52561304*x5^2+8443456*x5*x6-3184536*x6^2+15869383*x1-2326028*x2+15770498*x3-42544231*x4+47610560*x5-4542562*x6-2523880, -4868992*x1^3+32263630*x1^2*x2+34721976*x1^2*x3+20982140*x1^2*x4-7871668*x1^2*x5-8728440*x1^2*x6-10507577*x1*x2^2+38284676*x1*x2*x3-27598109*x1*x2*x4+78227493*x1*x2*x5+4449587*x1*x2*x6-23259264*x1*x3^2-39329624*x1*x3*x4+76393960*x1*x3*x5-39697064*x1*x3*x6+16452638*x1*x4^2+8414788*x1*x4*x5-4297868*x1*x4*x6+14208110*x1*x5^2+4398980*x1*x5*x6+30984190*x1*x6^2-13274261*x2^3+51589842*x2^2*x3-1241027*x2^2*x4+22323446*x2^2*x5+17849505*x2^2*x6-15466668*x2*x3^2+2221400*x2*x3*x4+39624724*x2*x3*x5-61848636*x2*x3*x6+35608159*x2*x4^2-76548845*x2*x4*x5+32445937*x2*x4*x6+83606730*x2*x5^2-1740302*x2*x5*x6+16796826*x2*x6^2+3851792*x3^3+10685724*x3^2*x4-26330892*x3^2*x5+14844060*x3^2*x6-7822494*x3*x4^2-23143804*x3*x4*x5+14867812*x3*x4*x6+34116490*x3*x5^2-58303428*x3*x5*x6+5797762*x3*x6^2-11640806*x4^3+37992804*x4^2*x5-25116626*x4^2*x6-30041260*x4*x5^2+19176418*x4*x5*x6-22397228*x4*x6^2+23473998*x5^3-1940970*x5^2*x6+22261360*x5*x6^2-20505680*x6^3-1564496*x1^2+7898523*x1*x2+48846144*x1*x3+9663290*x1*x4+25225782*x1*x5-8258422*x1*x6-32470992*x2^2+47502852*x2*x3-11042785*x2*x4+49926780*x2*x5+6676334*x2*x6-16683324*x3^2-13875628*x3*x4+41152836*x3*x5-34072596*x3*x6+20956048*x4^2-31149992*x4*x5+16685258*x4*x6+49921018*x5^2-17459028*x5*x6+27548600*x6^2+33018752*x1+15770498*x2+1196842*x3-15967864*x4+58917022*x5-29932266*x6+23751226, 1756936*x1^3-8889852*x1^2*x2+20982140*x1^2*x3+17621048*x1^2*x4-1086052*x1^2*x5+2367930*x1^2*x6+1771815*x1*x2^2-27598109*x1*x2*x3-46786060*x1*x2*x4+22974756*x1*x2*x5-8575699*x1*x2*x6-19664812*x1*x3^2+32905276*x1*x3*x4+8414788*x1*x3*x5-4297868*x1*x3*x6+60221136*x1*x4^2-30271008*x1*x4*x5+16254660*x1*x4*x6+17230458*x1*x5^2+12786158*x1*x5*x6+22857068*x1*x6^2+47461556*x2^3-1241027*x2^2*x3+26025442*x2^2*x4-36311783*x2^2*x5-5343255*x2^2*x6+1110700*x2*x3^2+71216318*x2*x3*x4-76548845*x2*x3*x5+32445937*x2*x3*x6-105423858*x2*x4^2+121571468*x2*x4*x5-28718016*x2*x4*x6-58463497*x2*x5^2-16405034*x2*x5*x6-41541916*x2*x6^2+3561908*x3^3-7822494*x3^2*x4-11571902*x3^2*x5+7433906*x3^2*x6-34922418*x3*x4^2+75985608*x3*x4*x5-50233252*x3*x4*x6-30041260*x3*x5^2+19176418*x3*x5*x6-22397228*x3*x6^2+45859504*x4^3-43757340*x4^2*x5+34054740*x4^2*x6+44169028*x4*x5^2+9021464*x4*x5*x6+56705848*x4*x6^2-11350358*x5^3+1832444*x5^2*x6-9174464*x5*x6^2+11962528*x6^3-8230572*x1^2+16022151*x1*x2+9663290*x1*x3-20383516*x1*x4+19893514*x1*x5-16449358*x1*x6+20793594*x2^2-11042785*x2*x3+7583102*x2*x4-30363266*x2*x5+30015366*x2*x6-6937814*x3^2+41912096*x3*x4-31149992*x3*x5+16685258*x3*x6-18602550*x4^2+52802196*x4*x5-25636112*x4*x6-21504014*x5^2+8604776*x5*x6-14934304*x6^2+27159978*x1-42544231*x2-15967864*x3+58209406*x4-22705154*x5+20325284*x6-7763622, 105592*x1^3-6656950*x1^2*x2-7871668*x1^2*x3-1086052*x1^2*x4-1677256*x1^2*x5+397478*x1^2*x6+39833981*x1*x2^2+78227493*x1*x2*x3+22974756*x1*x2*x4-34862*x1*x2*x5-14220914*x1*x2*x6+38196980*x1*x3^2+8414788*x1*x3*x4+28416220*x1*x3*x5+4398980*x1*x3*x6-15135504*x1*x4^2+34460916*x1*x4*x5+12786158*x1*x4*x6-8729814*x1*x5^2-9547564*x1*x5*x6-4467088*x1*x6^2-23925350*x2^3+22323446*x2^2*x3-36311783*x2^2*x4+103231252*x2^2*x5+38958894*x2^2*x6+19812362*x2*x3^2-76548845*x2*x3*x4+167213460*x2*x3*x5-1740302*x2*x3*x6+60785734*x2*x4^2-116926994*x2*x4*x5-16405034*x2*x4*x6+103079592*x2*x5^2+44122596*x2*x5*x6+42286600*x2*x6^2-8776964*x3^3-11571902*x3^2*x4+34116490*x3^2*x5-29151714*x3^2*x6+37992804*x3*x4^2-60082520*x3*x4*x5+19176418*x3*x4*x6+70421994*x3*x5^2-3881940*x3*x5*x6+22261360*x3*x6^2-14585780*x4^3+44169028*x4^2*x5+4510732*x4^2*x6-34051074*x4*x5^2+3664888*x4*x5*x6-9174464*x4*x6^2+25356100*x5^3+21173256*x5^2*x6+40400272*x5*x6^2+11169728*x6^3-2278084*x1^2+19860298*x1*x2+25225782*x1*x3+19893514*x1*x4-13737560*x1*x5-8435036*x1*x6-25646562*x2^2+49926780*x2*x3-30363266*x2*x4+105122608*x2*x5+8443456*x2*x6+20576418*x3^2-31149992*x3*x4+99842036*x3*x5-17459028*x3*x6+26401098*x4^2-43008028*x4*x5+8604776*x4*x6+55606740*x5^2+8709528*x5*x6+20574752*x6^2-5578786*x1+47610560*x2+58917022*x3-22705154*x4+70529124*x5+6837024*x6+29927948, 4599176*x1^3-30560941*x1^2*x2-8728440*x1^2*x3+2367930*x1^2*x4+397478*x1^2*x5+2602978*x1^2*x6+26404066*x1*x2^2+4449587*x1*x2*x3-8575699*x1*x2*x4-14220914*x1*x2*x5+25252156*x1*x2*x6-19848532*x1*x3^2-4297868*x1*x3*x4+4398980*x1*x3*x5+61968380*x1*x3*x6+8127330*x1*x4^2+12786158*x1*x4*x5+45714136*x1*x4*x6-4773782*x1*x5^2-8934176*x1*x5*x6-18332304*x1*x6^2+45796446*x2^3+17849505*x2^2*x3-5343255*x2^2*x4+38958894*x2^2*x5-64105730*x2^2*x6-30924318*x2*x3^2+32445937*x2*x3*x4-1740302*x2*x3*x5+33593652*x2*x3*x6-14359008*x2*x4^2-16405034*x2*x4*x5-83083832*x2*x4*x6+22061298*x2*x5^2+84573200*x2*x5*x6+53713584*x2*x6^2+4948020*x3^3+7433906*x3^2*x4-29151714*x3^2*x5+5797762*x3^2*x6-25116626*x3*x4^2+19176418*x3*x4*x5-44794456*x3*x4*x6-1940970*x3*x5^2+44522720*x3*x5*x6-61517040*x3*x6^2+11351580*x4^3+4510732*x4^2*x5+56705848*x4^2*x6+1832444*x4*x5^2-18348928*x4*x5*x6+35887584*x4*x6^2+7057752*x5^3+40400272*x5^2*x6+33509184*x5*x6^2+46860032*x6^3-6750768*x1^2+19551604*x1*x2-8258422*x1*x3-16449358*x1*x4-8435036*x1*x5-7932112*x1*x6-16187207*x2^2+6676334*x2*x3+30015366*x2*x4+8443456*x2*x5-6369072*x2*x6-17036298*x3^2+16685258*x3*x4-17459028*x3*x5+55097200*x3*x6-12818056*x4^2+8604776*x4*x5-29868608*x4*x6+4354764*x5^2+41149504*x5*x6-19496832*x6^2-1478078*x1-4542562*x2-29932266*x3+20325284*x4+6837024*x5+66687616*x6-10650840];
#     F_hom = sort([SG.homogenize(R, f) for f in F], by = p -> total_degree(p))
#     h = -23445*x1^2 - 25236*x1*x2 - 11589*x2^2 - 1538*x1*x3 - 27792*x2*x3 - 19380*x3^2 + 22256*x1*x4 - 25670*x2*x4 - 14762*x3*x4 - 26962*x4^2 + 5830*x1*x5 + 17628*x2*x5 - 13016*x3*x5 + 13007*x4*x5 - 14723*x5^2 + 3497*x1*x6 + 1019*x2*x6 + 20894*x3*x6 + 31787*x4*x6 + 388*x5*x6 - 21117*x6^2 - 17450*x0 - 21020*x1 - 105*x2 + 11663*x3 - 28459*x4 + 28592*x5 + 6164*x6
#     gb = SG.f45sat(F_hom, h, verbose = 1)
#     gb_tes = saturation(Ideal(R, F_hom), Ideal(R, h))[1]
#     @test is_eq(Ideal(R, gb), gb_tes)
# end


# @testset "cyclic 4 sigtails" begin
#     R, (x, y, z, w) = Singular.PolynomialRing(Singular.Fp(101), ["x", "y", "z", "w"])
#     I = SG.cyclic([x,y,z,w])
#     dat = SG.f5setup(I, trace_sig_tail_tags = [:f, :g])
#     G, H, pairs = SG.pairs_and_basis(dat, length(I))
#     SG.f5core!(dat, G, H, pairs, interreduction = false)
#     basis_sigs = [(i, g[1]) for i in keys(G) for g in G[i]]
#     gb = [R(dat.ctx, s) for s in basis_sigs]
#     projs = [R(dat.ctx.po, SG.project(dat.ctx, s)) for s in basis_sigs]
#     gb_s = [std(Ideal(R, I[1:k])) for k in 1:3]
#     for (p, g, sig) in zip(projs, gb, basis_sigs)
#         isone(sig[1]) && continue
#         k = sig[1]
#         @test iszero(Singular.reduce(p*I[k] - g, gb_s[k - 1]))
#     end
# end

# @testset "cyclic 6 sigtails" begin
#     R, (x1, x2, x3, x4, x5, x6) = Singular.PolynomialRing(Singular.Fp(101), ["x$(i)" for i in 1:6])
#     I = SG.cyclic([x1,x2,x3,x4,x5,x6])
#     dat = SG.f5setup(I, trace_sig_tail_tags = [:f, :g])
#     G, H, pairs = SG.pairs_and_basis(dat, length(I))
#     SG.f5core!(dat, G, H, pairs, interreduction = false)
#     basis_sigs = [(i, g[1]) for i in keys(G) for g in G[i]]
#     gb = [R(dat.ctx, s) for s in basis_sigs]
#     projs = [R(dat.ctx.po, SG.project(dat.ctx, s)) for s in basis_sigs]
#     gb_s = [std(Ideal(R, I[1:k])) for k in 1:5]
#     for (p, g, sig) in zip(projs, gb, basis_sigs)
#         isone(sig[1]) && continue
#         k = sig[1]
#         @test iszero(Singular.reduce(p*I[k] - g, gb_s[k - 1]))
#     end
# end

# @testset "cyclic 6" begin
#     R, (x1, x2, x3, x4, x5, x6) = Singular.PolynomialRing(Singular.Fp(101), ["x$(i)" for i in 1:6])
#     I = SG.cyclic([x1,x2,x3,x4,x5,x6])
#     gb = SG.f5(I, interreduction = false)
#     @test SG.is_gb(gb)
# end

# @testset "katsura 6 interreduction" begin
#     R, (x1, x2, x3, x4, x5, x6) = Singular.PolynomialRing(Singular.Fp(65521), ["x$(i)" for i in 1:6])
#     I = [x1+2*x2+2*x3+2*x4+2*x5+2*x6-1,
#          x1^2+2*x2^2+2*x3^2+2*x4^2+2*x5^2+2*x6^2-x1,
#          2*x1*x2+2*x2*x3+2*x3*x4+2*x4*x5+2*x5*x6-x2,
#          x2^2+2*x1*x3+2*x2*x4+2*x3*x5+2*x4*x6-x3,
#          2*x2*x3+2*x1*x4+2*x2*x5+2*x3*x6-x4,
#          x3^2+2*x2*x4+2*x1*x5+2*x2*x6-x5]
#     gb = SG.f5(I)
#     @test length(gb) == 22
# end

# @testset "small-decomp" begin
#     R, (x, y, z) = Singular.PolynomialRing(Singular.Fp(101), ["x", "y", "z"])
#     I = [x*y, x*z]
#     gb = decompose(I, interreduction = false)
#     @test SG.is_gb(gb)
#     @test is_eq(Ideal(R, gb), fancy_loop(I))
# end

# @testset "cyclic 4 decomp" begin
#     R, (x, y, z, w) = Singular.PolynomialRing(Singular.Fp(101), ["x", "y", "z", "w"])
#     I = SG.cyclic([x,y,z,w])
#     gb = decompose(I, interreduction = false)
#     @test SG.is_gb(gb)
#     @test is_eq(Ideal(R, gb), fancy_loop(I))
# end

# @testset "cyclic 6 decomp" begin
#     R, (x1, x2, x3, x4, x5, x6) = Singular.PolynomialRing(Singular.Fp(101), ["x$(i)" for i in 1:6])
#     I = SG.cyclic([x1,x2,x3,x4,x5,x6])
#     gb = decompose(I, interreduction = false)
#     @test SG.is_gb(gb)
#     @test is_eq(Ideal(R, gb), fancy_loop(I))
# end

# @testset "singhypcritpoints decomp" begin
#     R, (x1, x2, x3, x4)  = Singular.PolynomialRing(Singular.Fp(65521), ["x1", "x2", "x3", "x4"])
#     I = [2297232*x1^4+10816588*x1^3*x2-19696652*x1^3*x3+12014836*x1^3*x4+19038581*x1^2*x2^2+25140479*x1^2*x2*x3-124056256*x1^2*x2*x4-19352961*x1^2*x3^2+30086207*x1^2*x3*x4-15861565*x1^2*x4^2-64545276*x1*x2^3-3395230*x1*x2^2*x3+125153935*x1*x2^2*x4-10319588*x1*x2*x3^2+5839912*x1*x2*x3*x4+112915639*x1*x2*x4^2+12114032*x1*x3^3+32314614*x1*x3^2*x4-5646418*x1*x3*x4^2-3823868*x1*x4^3+40572828*x2^4-42051502*x2^3*x3-17361686*x2^3*x4+66618627*x2^2*x3^2-61020343*x2^2*x3*x4-66491064*x2^2*x4^2+16298428*x2*x3^3+46623254*x2*x3^2*x4-26720875*x2*x3*x4^2-16047619*x2*x4^3+15073900*x3^4+9644976*x3^3*x4-9790086*x3^2*x4^2-9372130*x3*x4^3+4661500*x4^4-39813328*x1^3-9400295*x1^2*x2-1289811*x1^2*x3+64756487*x1^2*x4-41226416*x1*x2^2+22255617*x1*x2*x3+115474646*x1*x2*x4+54583668*x1*x3^2+150465505*x1*x3*x4-19224417*x1*x4^2+52554279*x2^3-1318549*x2^2*x3-91874169*x2^2*x4+119183502*x2*x3^2-131012023*x2*x3*x4-88321124*x2*x4^2+41605616*x3^3+58052114*x3^2*x4-70772721*x3*x4^2+3123219*x4^3+99968607*x1^2-17533608*x1*x2+133696391*x1*x3-71771275*x1*x4+20484256*x2^2+10206682*x2*x3-58141098*x2*x4+72704712*x3^2-111938286*x3*x4-5946966*x4^2-46338000*x1+12230767*x2-23665371*x3+7665457*x4+9313394, 10816588*x1^3+38077162*x1^2*x2+25140479*x1^2*x3-124056256*x1^2*x4-193635828*x1*x2^2-6790460*x1*x2*x3+250307870*x1*x2*x4-10319588*x1*x3^2+5839912*x1*x3*x4+112915639*x1*x4^2+162291312*x2^3-126154506*x2^2*x3-52085058*x2^2*x4+133237254*x2*x3^2-122040686*x2*x3*x4-132982128*x2*x4^2+16298428*x3^3+46623254*x3^2*x4-26720875*x3*x4^2-16047619*x4^3-9400295*x1^2-82452832*x1*x2+22255617*x1*x3+115474646*x1*x4+157662837*x2^2-2637098*x2*x3-183748338*x2*x4+119183502*x3^2-131012023*x3*x4-88321124*x4^2-17533608*x1+40968512*x2+10206682*x3-58141098*x4+12230767, -19696652*x1^3+25140479*x1^2*x2-38705922*x1^2*x3+30086207*x1^2*x4-3395230*x1*x2^2-20639176*x1*x2*x3+5839912*x1*x2*x4+36342096*x1*x3^2+64629228*x1*x3*x4-5646418*x1*x4^2-42051502*x2^3+133237254*x2^2*x3-61020343*x2^2*x4+48895284*x2*x3^2+93246508*x2*x3*x4-26720875*x2*x4^2+60295600*x3^3+28934928*x3^2*x4-19580172*x3*x4^2-9372130*x4^3-1289811*x1^2+22255617*x1*x2+109167336*x1*x3+150465505*x1*x4-1318549*x2^2+238367004*x2*x3-131012023*x2*x4+124816848*x3^2+116104228*x3*x4-70772721*x4^2+133696391*x1+10206682*x2+145409424*x3-111938286*x4-23665371, 12014836*x1^3-124056256*x1^2*x2+30086207*x1^2*x3-31723130*x1^2*x4+125153935*x1*x2^2+5839912*x1*x2*x3+225831278*x1*x2*x4+32314614*x1*x3^2-11292836*x1*x3*x4-11471604*x1*x4^2-17361686*x2^3-61020343*x2^2*x3-132982128*x2^2*x4+46623254*x2*x3^2-53441750*x2*x3*x4-48142857*x2*x4^2+9644976*x3^3-19580172*x3^2*x4-28116390*x3*x4^2+18646000*x4^3+64756487*x1^2+115474646*x1*x2+150465505*x1*x3-38448834*x1*x4-91874169*x2^2-131012023*x2*x3-176642248*x2*x4+58052114*x3^2-141545442*x3*x4+9369657*x4^2-71771275*x1-58141098*x2-111938286*x3-11893932*x4+7665457]
#     gb = decompose(I, interreduction = false)
#     @test SG.is_gb(gb)
#     @test is_eq(Ideal(R, gb), fancy_loop(I))
#     gb = decompose(I)
#     @test SG.is_gb(gb)
#     @test length(gb) == length(gens(fancy_loop(I, interreduce = true)))
# end
