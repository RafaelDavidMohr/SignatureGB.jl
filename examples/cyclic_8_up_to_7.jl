using Singular
using SignatureGB
R, (x1,x2,x3,x4,x5,x6,x7,x8) = Singular.PolynomialRing(Fp(101), ["x1", "x2", "x3", "x4", "x5", "x6", "x7", "x8"])
I = spoly{n_Zp}[x1 + x2 + x3 + x4 + x5 + x6 + x7 + x8, x1*x2 + x2*x3 + x3*x4 + x4*x5 + x5*x6 + x6*x7 + x1*x8 + x7*x8, x1*x2*x3 + x2*x3*x4 + x3*x4*x5 + x4*x5*x6 + x5*x6*x7 + x1*x2*x8 + x1*x7*x8 + x6*x7*x8, x1*x2*x3*x4 + x2*x3*x4*x5 + x3*x4*x5*x6 + x4*x5*x6*x7 + x1*x2*x3*x8 + x1*x2*x7*x8 + x1*x6*x7*x8 + x5*x6*x7*x8, x1*x2*x3*x4*x5 + x2*x3*x4*x5*x6 + x3*x4*x5*x6*x7 + x1*x2*x3*x4*x8 + x1*x2*x3*x7*x8 + x1*x2*x6*x7*x8 + x1*x5*x6*x7*x8 + x4*x5*x6*x7*x8, x1*x2*x3*x4*x5*x6 + x2*x3*x4*x5*x6*x7 + x1*x2*x3*x4*x5*x8 + x1*x2*x3*x4*x7*x8 + x1*x2*x3*x6*x7*x8 + x1*x2*x5*x6*x7*x8 + x1*x4*x5*x6*x7*x8 + x3*x4*x5*x6*x7*x8, x1*x2*x3*x4*x5*x6*x7 + x1*x2*x3*x4*x5*x6*x8 + x1*x2*x3*x4*x5*x7*x8 + x1*x2*x3*x4*x6*x7*x8 + x1*x2*x3*x5*x6*x7*x8 + x1*x2*x4*x5*x6*x7*x8 + x1*x3*x4*x5*x6*x7*x8 + x2*x3*x4*x5*x6*x7*x8]
comp_ideal = gens(R)
SignatureGB.f5(comp_ideal)
gb = SignatureGB.f5(I, verbose = true)
println("is Gröbner Basis: $(SignatureGB.is_gb(gb))")
