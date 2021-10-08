using Singular
using SignatureGB
R, (x1,x2,x3,x4,x5,x6,x7) = Singular.PolynomialRing(Fp(101), ["x1", "x2", "x3", "x4", "x5", "x6", "x7"])
I = spoly{n_Zp}[x1 + x2 + x3 + x4 + x5 + x6 + x7, x1*x2 + x2*x3 + x3*x4 + x4*x5 + x5*x6 + x1*x7 + x6*x7, x1*x2*x3 + x2*x3*x4 + x3*x4*x5 + x4*x5*x6 + x1*x2*x7 + x1*x6*x7 + x5*x6*x7, x1*x2*x3*x4 + x2*x3*x4*x5 + x3*x4*x5*x6 + x1*x2*x3*x7 + x1*x2*x6*x7 + x1*x5*x6*x7 + x4*x5*x6*x7, x1*x2*x3*x4*x5 + x2*x3*x4*x5*x6 + x1*x2*x3*x4*x7 + x1*x2*x3*x6*x7 + x1*x2*x5*x6*x7 + x1*x4*x5*x6*x7 + x3*x4*x5*x6*x7, x1*x2*x3*x4*x5*x6 + x1*x2*x3*x4*x5*x7 + x1*x2*x3*x4*x6*x7 + x1*x2*x3*x5*x6*x7 + x1*x2*x4*x5*x6*x7 + x1*x3*x4*x5*x6*x7 + x2*x3*x4*x5*x6*x7, x1*x2*x3*x4*x5*x6*x7 - 1]
comp_ideal = gens(R)
SignatureGB.f5(comp_ideal)
gb = SignatureGB.f5(I, verbose = true)
println(SignatureGB.is_gb(gb))
