using SignatureGB
using Singular
P, (x1, x2, x3, x4, x5, x6, x7, x8, x9)  = Singular.PolynomialRing(Fp(65521), ["x1", "x2", "x3", "x4", "x5", "x6", "x7", "x8", "x9"]);
gb = SignatureGB.f5([x1, x2, x3, x4, x5, x6, x7, x8, x9]);F = [361*x1^2*x4^2+1748*x1^2*x4*x9+2209*x1^2*x7^2+2116*x1^2*x8^2+2116*x1^2*x9^2-7896*x1*x3*x4*x7+1026*x1*x3*x4*x8-7050*x1*x3*x6*x7-1034*x1*x3*x7^2-2392*x1*x3*x7*x8+2484*x1*x3*x8*x9+1330*x1*x4^3+3220*x1*x4^2*x9+1254*x1*x4*x6*x8-5704*x1*x5*x8^2+3036*x1*x6*x8*x9-5546*x1*x7^2*x9+920*x1*x8^2*x9+625*x2^4+1000*x2^3*x3+400*x2^2*x3^2+2050*x2^2*x4*x7+4450*x2^2*x4*x9-300*x2^2*x5*x7+1640*x2*x3*x4*x7+3560*x2*x3*x4*x9-240*x2*x3*x5*x7+7056*x3^2*x4^2+12600*x3^2*x4*x6+1848*x3^2*x4*x7+6781*x3^2*x6^2+3486*x3^2*x6*x7+1526*x3^2*x7^2+729*x3^2*x8^2+1890*x3*x4^2*x8+9912*x3*x4*x7*x9-1700*x3*x5*x6^2-1350*x3*x5*x6*x7-340*x3*x5*x6*x9+3224*x3*x5*x7*x8-270*x3*x5*x7*x9+8850*x3*x6*x7*x9+1782*x3*x6*x8^2-5712*x3*x6*x8*x9+1298*x3*x7^2*x9-5056*x3*x7*x8*x9+1225*x4^4+2310*x4^2*x6*x8+1681*x4^2*x7^2+7298*x4^2*x7*x9+7921*x4^2*x9^2-492*x4*x5*x7^2-1068*x4*x5*x7*x9+625*x5^2*x6^2+250*x5^2*x6*x9+36*x5^2*x7^2+3844*x5^2*x8^2+25*x5^2*x9^2+4200*x5*x6*x8*x9-1240*x5*x8^2*x9+840*x5*x8*x9^2+1089*x6^2*x8^2+3481*x7^2*x9^2+7156*x8^2*x9^2-1786*x1*x3*x7+5980*x1*x4*x8-3040*x1*x4*x9-7360*x1*x9^2+3192*x3^2*x4+2850*x3^2*x6+418*x3^2*x7-3380*x3*x4*x7-6528*x3*x6*x7-5184*x3*x7^2+2242*x3*x7*x9-4320*x3*x8*x9-5600*x4^2*x9-8060*x4*x5*x8+1300*x4*x8*x9+4800*x5*x6*x7+960*x5*x7*x9-5280*x6*x8*x9+16128*x7*x8*x9+361*x3^2+4225*x4^2+9216*x7^2+6400*x9^2, 2500*x2^3+3000*x2^2*x3+800*x2*x3^2+4100*x2*x4*x7+8900*x2*x4*x9-600*x2*x5*x7+1640*x3*x4*x7+3560*x3*x4*x9-240*x3*x5*x7, -7896*x1*x4*x7+1026*x1*x4*x8-7050*x1*x6*x7-1034*x1*x7^2-2392*x1*x7*x8+2484*x1*x8*x9+1000*x2^3+800*x2^2*x3+1640*x2*x4*x7+3560*x2*x4*x9-240*x2*x5*x7+14112*x3*x4^2+25200*x3*x4*x6+3696*x3*x4*x7+13562*x3*x6^2+6972*x3*x6*x7+3052*x3*x7^2+1458*x3*x8^2+1890*x4^2*x8+9912*x4*x7*x9-1700*x5*x6^2-1350*x5*x6*x7-340*x5*x6*x9+3224*x5*x7*x8-270*x5*x7*x9+8850*x6*x7*x9+1782*x6*x8^2-5712*x6*x8*x9+1298*x7^2*x9-5056*x7*x8*x9-1786*x1*x7+6384*x3*x4+5700*x3*x6+836*x3*x7-3380*x4*x7-6528*x6*x7-5184*x7^2+2242*x7*x9-4320*x8*x9+722*x3, 722*x1^2*x4+1748*x1^2*x9-7896*x1*x3*x7+1026*x1*x3*x8+3990*x1*x4^2+6440*x1*x4*x9+1254*x1*x6*x8+2050*x2^2*x7+4450*x2^2*x9+1640*x2*x3*x7+3560*x2*x3*x9+14112*x3^2*x4+12600*x3^2*x6+1848*x3^2*x7+3780*x3*x4*x8+9912*x3*x7*x9+4900*x4^3+4620*x4*x6*x8+3362*x4*x7^2+14596*x4*x7*x9+15842*x4*x9^2-492*x5*x7^2-1068*x5*x7*x9+5980*x1*x8-3040*x1*x9+3192*x3^2-3380*x3*x7-11200*x4*x9-8060*x5*x8+1300*x8*x9+8450*x4, -5704*x1*x8^2-300*x2^2*x7-240*x2*x3*x7-1700*x3*x6^2-1350*x3*x6*x7-340*x3*x6*x9+3224*x3*x7*x8-270*x3*x7*x9-492*x4*x7^2-1068*x4*x7*x9+1250*x5*x6^2+500*x5*x6*x9+72*x5*x7^2+7688*x5*x8^2+50*x5*x9^2+4200*x6*x8*x9-1240*x8^2*x9+840*x8*x9^2-8060*x4*x8+4800*x6*x7+960*x7*x9, -7050*x1*x3*x7+1254*x1*x4*x8+3036*x1*x8*x9+12600*x3^2*x4+13562*x3^2*x6+3486*x3^2*x7-3400*x3*x5*x6-1350*x3*x5*x7-340*x3*x5*x9+8850*x3*x7*x9+1782*x3*x8^2-5712*x3*x8*x9+2310*x4^2*x8+1250*x5^2*x6+250*x5^2*x9+4200*x5*x8*x9+2178*x6*x8^2+2850*x3^2-6528*x3*x7+4800*x5*x7-5280*x8*x9, 4418*x1^2*x7-7896*x1*x3*x4-7050*x1*x3*x6-2068*x1*x3*x7-2392*x1*x3*x8-11092*x1*x7*x9+2050*x2^2*x4-300*x2^2*x5+1640*x2*x3*x4-240*x2*x3*x5+1848*x3^2*x4+3486*x3^2*x6+3052*x3^2*x7+9912*x3*x4*x9-1350*x3*x5*x6+3224*x3*x5*x8-270*x3*x5*x9+8850*x3*x6*x9+2596*x3*x7*x9-5056*x3*x8*x9+3362*x4^2*x7+7298*x4^2*x9-984*x4*x5*x7-1068*x4*x5*x9+72*x5^2*x7+6962*x7*x9^2-1786*x1*x3+418*x3^2-3380*x3*x4-6528*x3*x6-10368*x3*x7+2242*x3*x9+4800*x5*x6+960*x5*x9+16128*x8*x9+18432*x7, 4232*x1^2*x8+1026*x1*x3*x4-2392*x1*x3*x7+2484*x1*x3*x9+1254*x1*x4*x6-11408*x1*x5*x8+3036*x1*x6*x9+1840*x1*x8*x9+1458*x3^2*x8+1890*x3*x4^2+3224*x3*x5*x7+3564*x3*x6*x8-5712*x3*x6*x9-5056*x3*x7*x9+2310*x4^2*x6+7688*x5^2*x8+4200*x5*x6*x9-2480*x5*x8*x9+840*x5*x9^2+2178*x6^2*x8+14312*x8*x9^2+5980*x1*x4-4320*x3*x9-8060*x4*x5+1300*x4*x9-5280*x6*x9+16128*x7*x9, 1748*x1^2*x4+4232*x1^2*x9+2484*x1*x3*x8+3220*x1*x4^2+3036*x1*x6*x8-5546*x1*x7^2+920*x1*x8^2+4450*x2^2*x4+3560*x2*x3*x4+9912*x3*x4*x7-340*x3*x5*x6-270*x3*x5*x7+8850*x3*x6*x7-5712*x3*x6*x8+1298*x3*x7^2-5056*x3*x7*x8+7298*x4^2*x7+15842*x4^2*x9-1068*x4*x5*x7+250*x5^2*x6+50*x5^2*x9+4200*x5*x6*x8-1240*x5*x8^2+1680*x5*x8*x9+6962*x7^2*x9+14312*x8^2*x9-3040*x1*x4-14720*x1*x9+2242*x3*x7-4320*x3*x8-5600*x4^2+1300*x4*x8+960*x5*x7-5280*x6*x8+16128*x7*x8+12800*x9];
println(@elapsed SignatureGB.f5([361*x1^2*x4^2+1748*x1^2*x4*x9+2209*x1^2*x7^2+2116*x1^2*x8^2+2116*x1^2*x9^2-7896*x1*x3*x4*x7+1026*x1*x3*x4*x8-7050*x1*x3*x6*x7-1034*x1*x3*x7^2-2392*x1*x3*x7*x8+2484*x1*x3*x8*x9+1330*x1*x4^3+3220*x1*x4^2*x9+1254*x1*x4*x6*x8-5704*x1*x5*x8^2+3036*x1*x6*x8*x9-5546*x1*x7^2*x9+920*x1*x8^2*x9+625*x2^4+1000*x2^3*x3+400*x2^2*x3^2+2050*x2^2*x4*x7+4450*x2^2*x4*x9-300*x2^2*x5*x7+1640*x2*x3*x4*x7+3560*x2*x3*x4*x9-240*x2*x3*x5*x7+7056*x3^2*x4^2+12600*x3^2*x4*x6+1848*x3^2*x4*x7+6781*x3^2*x6^2+3486*x3^2*x6*x7+1526*x3^2*x7^2+729*x3^2*x8^2+1890*x3*x4^2*x8+9912*x3*x4*x7*x9-1700*x3*x5*x6^2-1350*x3*x5*x6*x7-340*x3*x5*x6*x9+3224*x3*x5*x7*x8-270*x3*x5*x7*x9+8850*x3*x6*x7*x9+1782*x3*x6*x8^2-5712*x3*x6*x8*x9+1298*x3*x7^2*x9-5056*x3*x7*x8*x9+1225*x4^4+2310*x4^2*x6*x8+1681*x4^2*x7^2+7298*x4^2*x7*x9+7921*x4^2*x9^2-492*x4*x5*x7^2-1068*x4*x5*x7*x9+625*x5^2*x6^2+250*x5^2*x6*x9+36*x5^2*x7^2+3844*x5^2*x8^2+25*x5^2*x9^2+4200*x5*x6*x8*x9-1240*x5*x8^2*x9+840*x5*x8*x9^2+1089*x6^2*x8^2+3481*x7^2*x9^2+7156*x8^2*x9^2-1786*x1*x3*x7+5980*x1*x4*x8-3040*x1*x4*x9-7360*x1*x9^2+3192*x3^2*x4+2850*x3^2*x6+418*x3^2*x7-3380*x3*x4*x7-6528*x3*x6*x7-5184*x3*x7^2+2242*x3*x7*x9-4320*x3*x8*x9-5600*x4^2*x9-8060*x4*x5*x8+1300*x4*x8*x9+4800*x5*x6*x7+960*x5*x7*x9-5280*x6*x8*x9+16128*x7*x8*x9+361*x3^2+4225*x4^2+9216*x7^2+6400*x9^2, 2500*x2^3+3000*x2^2*x3+800*x2*x3^2+4100*x2*x4*x7+8900*x2*x4*x9-600*x2*x5*x7+1640*x3*x4*x7+3560*x3*x4*x9-240*x3*x5*x7, -7896*x1*x4*x7+1026*x1*x4*x8-7050*x1*x6*x7-1034*x1*x7^2-2392*x1*x7*x8+2484*x1*x8*x9+1000*x2^3+800*x2^2*x3+1640*x2*x4*x7+3560*x2*x4*x9-240*x2*x5*x7+14112*x3*x4^2+25200*x3*x4*x6+3696*x3*x4*x7+13562*x3*x6^2+6972*x3*x6*x7+3052*x3*x7^2+1458*x3*x8^2+1890*x4^2*x8+9912*x4*x7*x9-1700*x5*x6^2-1350*x5*x6*x7-340*x5*x6*x9+3224*x5*x7*x8-270*x5*x7*x9+8850*x6*x7*x9+1782*x6*x8^2-5712*x6*x8*x9+1298*x7^2*x9-5056*x7*x8*x9-1786*x1*x7+6384*x3*x4+5700*x3*x6+836*x3*x7-3380*x4*x7-6528*x6*x7-5184*x7^2+2242*x7*x9-4320*x8*x9+722*x3, 722*x1^2*x4+1748*x1^2*x9-7896*x1*x3*x7+1026*x1*x3*x8+3990*x1*x4^2+6440*x1*x4*x9+1254*x1*x6*x8+2050*x2^2*x7+4450*x2^2*x9+1640*x2*x3*x7+3560*x2*x3*x9+14112*x3^2*x4+12600*x3^2*x6+1848*x3^2*x7+3780*x3*x4*x8+9912*x3*x7*x9+4900*x4^3+4620*x4*x6*x8+3362*x4*x7^2+14596*x4*x7*x9+15842*x4*x9^2-492*x5*x7^2-1068*x5*x7*x9+5980*x1*x8-3040*x1*x9+3192*x3^2-3380*x3*x7-11200*x4*x9-8060*x5*x8+1300*x8*x9+8450*x4, -5704*x1*x8^2-300*x2^2*x7-240*x2*x3*x7-1700*x3*x6^2-1350*x3*x6*x7-340*x3*x6*x9+3224*x3*x7*x8-270*x3*x7*x9-492*x4*x7^2-1068*x4*x7*x9+1250*x5*x6^2+500*x5*x6*x9+72*x5*x7^2+7688*x5*x8^2+50*x5*x9^2+4200*x6*x8*x9-1240*x8^2*x9+840*x8*x9^2-8060*x4*x8+4800*x6*x7+960*x7*x9, -7050*x1*x3*x7+1254*x1*x4*x8+3036*x1*x8*x9+12600*x3^2*x4+13562*x3^2*x6+3486*x3^2*x7-3400*x3*x5*x6-1350*x3*x5*x7-340*x3*x5*x9+8850*x3*x7*x9+1782*x3*x8^2-5712*x3*x8*x9+2310*x4^2*x8+1250*x5^2*x6+250*x5^2*x9+4200*x5*x8*x9+2178*x6*x8^2+2850*x3^2-6528*x3*x7+4800*x5*x7-5280*x8*x9, 4418*x1^2*x7-7896*x1*x3*x4-7050*x1*x3*x6-2068*x1*x3*x7-2392*x1*x3*x8-11092*x1*x7*x9+2050*x2^2*x4-300*x2^2*x5+1640*x2*x3*x4-240*x2*x3*x5+1848*x3^2*x4+3486*x3^2*x6+3052*x3^2*x7+9912*x3*x4*x9-1350*x3*x5*x6+3224*x3*x5*x8-270*x3*x5*x9+8850*x3*x6*x9+2596*x3*x7*x9-5056*x3*x8*x9+3362*x4^2*x7+7298*x4^2*x9-984*x4*x5*x7-1068*x4*x5*x9+72*x5^2*x7+6962*x7*x9^2-1786*x1*x3+418*x3^2-3380*x3*x4-6528*x3*x6-10368*x3*x7+2242*x3*x9+4800*x5*x6+960*x5*x9+16128*x8*x9+18432*x7, 4232*x1^2*x8+1026*x1*x3*x4-2392*x1*x3*x7+2484*x1*x3*x9+1254*x1*x4*x6-11408*x1*x5*x8+3036*x1*x6*x9+1840*x1*x8*x9+1458*x3^2*x8+1890*x3*x4^2+3224*x3*x5*x7+3564*x3*x6*x8-5712*x3*x6*x9-5056*x3*x7*x9+2310*x4^2*x6+7688*x5^2*x8+4200*x5*x6*x9-2480*x5*x8*x9+840*x5*x9^2+2178*x6^2*x8+14312*x8*x9^2+5980*x1*x4-4320*x3*x9-8060*x4*x5+1300*x4*x9-5280*x6*x9+16128*x7*x9, 1748*x1^2*x4+4232*x1^2*x9+2484*x1*x3*x8+3220*x1*x4^2+3036*x1*x6*x8-5546*x1*x7^2+920*x1*x8^2+4450*x2^2*x4+3560*x2*x3*x4+9912*x3*x4*x7-340*x3*x5*x6-270*x3*x5*x7+8850*x3*x6*x7-5712*x3*x6*x8+1298*x3*x7^2-5056*x3*x7*x8+7298*x4^2*x7+15842*x4^2*x9-1068*x4*x5*x7+250*x5^2*x6+50*x5^2*x9+4200*x5*x6*x8-1240*x5*x8^2+1680*x5*x8*x9+6962*x7^2*x9+14312*x8^2*x9-3040*x1*x4-14720*x1*x9+2242*x3*x7-4320*x3*x8-5600*x4^2+1300*x4*x8+960*x5*x7-5280*x6*x8+16128*x7*x8+12800*x9], verbose=true));exit()
