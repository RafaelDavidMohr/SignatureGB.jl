using SignatureGB
using Singular
P, (x1, x2, x3, x4)  = Singular.PolynomialRing(Fp(65521), ["x1", "x2", "x3", "x4"]);
gb = SignatureGB.f5([x1, x2, x3, x4]);F = [3136*x1^4+6944*x1^2*x2^2-5823*x1^2*x3^2+8176*x1^2*x4^2-2414*x1*x2^2*x3-10650*x1*x2*x3^2+4133*x2^4+2550*x2^3*x3-6403*x2^2*x3^2+9052*x2^2*x4^2+9409*x3^4-14162*x3^2*x4^2+5329*x4^4-9744*x1^3+11360*x1^2*x3-13508*x1*x2^2-12000*x1*x2*x3+16878*x1*x3^2-6248*x1*x3*x4-12702*x1*x4^2+1496*x2^2*x4+6600*x2*x3*x4+13969*x1^2-11644*x1*x3-7040*x1*x4+2788*x2^2+12300*x2*x3+1936*x4^2-13120*x1+7216*x4+6724, 13888*x1^2*x2-4828*x1*x2*x3-10650*x1*x3^2+16532*x2^3+7650*x2^2*x3-12806*x2*x3^2+18104*x2*x4^2-27016*x1*x2-12000*x1*x3+2992*x2*x4+6600*x3*x4+5576*x2+12300*x3, -11646*x1^2*x3-2414*x1*x2^2-21300*x1*x2*x3+2550*x2^3-12806*x2^2*x3+37636*x3^3-28324*x3*x4^2+11360*x1^2-12000*x1*x2+33756*x1*x3-6248*x1*x4+6600*x2*x4-11644*x1+12300*x2, 16352*x1^2*x4+18104*x2^2*x4-28324*x3^2*x4+21316*x4^3-6248*x1*x3-25404*x1*x4+1496*x2^2+6600*x2*x3-7040*x1+3872*x4+7216];
gb = SignatureGB.f5([3136*x1^4+6944*x1^2*x2^2-5823*x1^2*x3^2+8176*x1^2*x4^2-2414*x1*x2^2*x3-10650*x1*x2*x3^2+4133*x2^4+2550*x2^3*x3-6403*x2^2*x3^2+9052*x2^2*x4^2+9409*x3^4-14162*x3^2*x4^2+5329*x4^4-9744*x1^3+11360*x1^2*x3-13508*x1*x2^2-12000*x1*x2*x3+16878*x1*x3^2-6248*x1*x3*x4-12702*x1*x4^2+1496*x2^2*x4+6600*x2*x3*x4+13969*x1^2-11644*x1*x3-7040*x1*x4+2788*x2^2+12300*x2*x3+1936*x4^2-13120*x1+7216*x4+6724, 13888*x1^2*x2-4828*x1*x2*x3-10650*x1*x3^2+16532*x2^3+7650*x2^2*x3-12806*x2*x3^2+18104*x2*x4^2-27016*x1*x2-12000*x1*x3+2992*x2*x4+6600*x3*x4+5576*x2+12300*x3, -11646*x1^2*x3-2414*x1*x2^2-21300*x1*x2*x3+2550*x2^3-12806*x2^2*x3+37636*x3^3-28324*x3*x4^2+11360*x1^2-12000*x1*x2+33756*x1*x3-6248*x1*x4+6600*x2*x4-11644*x1+12300*x2, 16352*x1^2*x4+18104*x2^2*x4-28324*x3^2*x4+21316*x4^3-6248*x1*x3-25404*x1*x4+1496*x2^2+6600*x2*x3-7040*x1+3872*x4+7216], verbose=true);[leading_monomial(g) for g in gb];exit()
