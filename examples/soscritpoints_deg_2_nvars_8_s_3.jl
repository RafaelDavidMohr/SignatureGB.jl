using SignatureGB
using Singular
P, (x1, x2, x3, x4, x5, x6, x7, x8)  = Singular.PolynomialRing(Fp(65521), ["x1", "x2", "x3", "x4", "x5", "x6", "x7", "x8"]);
gb = SignatureGB.f5([x1, x2, x3, x4, x5, x6, x7, x8]);F = [7625*x1^4+3080*x1^2*x2^2+4760*x1^2*x2*x6+200*x1^2*x2*x7-280*x1^2*x5*x8+600*x1^2*x6*x8+5929*x2^4+770*x2^3*x7+9*x2^2*x4^2-1078*x2^2*x5*x8+784*x2^2*x6^2+2310*x2^2*x6*x8+25*x2^2*x7^2+36*x2*x3*x4*x7+360*x2*x4^2*x7+102*x2*x4*x7*x8-70*x2*x5*x7*x8+150*x2*x6*x7*x8+36*x3^2*x7^2+720*x3*x4*x7^2+204*x3*x7^2*x8+3600*x4^2*x7^2+2040*x4*x7^2*x8+49*x5^2*x8^2-210*x5*x6*x8^2+225*x6^2*x8^2+289*x7^2*x8^2-2550*x1^2*x3+9690*x1^2*x5-15810*x1^2*x6-13940*x1^2*x7+2240*x1^2*x8+8624*x2^2*x8-840*x2*x3*x6-306*x2*x4^2+234*x2*x4*x5+3192*x2*x5*x6-5208*x2*x6^2-4592*x2*x6*x7+560*x2*x7*x8-612*x3*x4*x7+468*x3*x5*x7-6120*x4^2*x7+4680*x4*x5*x7-1734*x4*x7*x8+1326*x5*x7*x8-784*x5*x8^2+1680*x6*x8^2+225*x3^2-1710*x3*x5+2790*x3*x6+2460*x3*x7+2601*x4^2-3978*x4*x5+4770*x5^2-10602*x5*x6-9348*x5*x7+8649*x6^2+15252*x6*x7+6724*x7^2+3136*x8^2, 6160*x1^2*x2+4760*x1^2*x6+200*x1^2*x7+23716*x2^3+2310*x2^2*x7+18*x2*x4^2-2156*x2*x5*x8+1568*x2*x6^2+4620*x2*x6*x8+50*x2*x7^2+36*x3*x4*x7+360*x4^2*x7+102*x4*x7*x8-70*x5*x7*x8+150*x6*x7*x8+17248*x2*x8-840*x3*x6-306*x4^2+234*x4*x5+3192*x5*x6-5208*x6^2-4592*x6*x7+560*x7*x8, 36*x2*x4*x7+72*x3*x7^2+720*x4*x7^2+204*x7^2*x8-2550*x1^2-840*x2*x6-612*x4*x7+468*x5*x7+450*x3-1710*x5+2790*x6+2460*x7, 18*x2^2*x4+36*x2*x3*x7+720*x2*x4*x7+102*x2*x7*x8+720*x3*x7^2+7200*x4*x7^2+2040*x7^2*x8-612*x2*x4+234*x2*x5-612*x3*x7-12240*x4*x7+4680*x5*x7-1734*x7*x8+5202*x4-3978*x5, -280*x1^2*x8-1078*x2^2*x8-70*x2*x7*x8+98*x5*x8^2-210*x6*x8^2+9690*x1^2+234*x2*x4+3192*x2*x6+468*x3*x7+4680*x4*x7+1326*x7*x8-784*x8^2-1710*x3-3978*x4+9540*x5-10602*x6-9348*x7, 4760*x1^2*x2+600*x1^2*x8+1568*x2^2*x6+2310*x2^2*x8+150*x2*x7*x8-210*x5*x8^2+450*x6*x8^2-15810*x1^2-840*x2*x3+3192*x2*x5-10416*x2*x6-4592*x2*x7+1680*x8^2+2790*x3-10602*x5+17298*x6+15252*x7, 200*x1^2*x2+770*x2^3+50*x2^2*x7+36*x2*x3*x4+360*x2*x4^2+102*x2*x4*x8-70*x2*x5*x8+150*x2*x6*x8+72*x3^2*x7+1440*x3*x4*x7+408*x3*x7*x8+7200*x4^2*x7+4080*x4*x7*x8+578*x7*x8^2-13940*x1^2-4592*x2*x6+560*x2*x8-612*x3*x4+468*x3*x5-6120*x4^2+4680*x4*x5-1734*x4*x8+1326*x5*x8+2460*x3-9348*x5+15252*x6+13448*x7, -280*x1^2*x5+600*x1^2*x6-1078*x2^2*x5+2310*x2^2*x6+102*x2*x4*x7-70*x2*x5*x7+150*x2*x6*x7+204*x3*x7^2+2040*x4*x7^2+98*x5^2*x8-420*x5*x6*x8+450*x6^2*x8+578*x7^2*x8+2240*x1^2+8624*x2^2+560*x2*x7-1734*x4*x7+1326*x5*x7-1568*x5*x8+3360*x6*x8+6272*x8];
sort!(F, by = p -> leading_monomial(p))
println(@elapsed SignatureGB.f5(F, verbose=true));exit()
