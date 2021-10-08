using SignatureGB
using Singular
P, (x1, x2, x3, x4, x5)  = Singular.PolynomialRing(Fp(65521), ["x1", "x2", "x3", "x4", "x5"]);
gb = SignatureGB.f5([x1, x2, x3, x4, x5]);F = [2500*x1^4-6000*x1^3*x5+10737*x1^2*x2^2-66*x1^2*x2*x4+700*x1^2*x3^2+2809*x1^2*x4^2+3600*x1^2*x5^2+5616*x1*x2*x3^2-3264*x1*x2*x3*x4+9840*x1*x2*x4*x5+17472*x1*x2*x5^2+7632*x1*x3^2*x4-840*x1*x3^2*x5+1764*x2^2*x4^2-588*x2*x3^2*x4+5233*x3^4+289*x3^2*x4^2-850*x3*x4^2*x5-3094*x3*x4*x5^2+625*x4^2*x5^2+4550*x4*x5^3+8281*x5^4+4760*x1^2*x2-9388*x1^2*x4-5538*x1*x2*x3+7626*x1*x2*x5+288*x1*x3^2-8784*x1*x3*x4+18352*x1*x4*x5+6734*x1*x5^2+2100*x2^2*x4-350*x2*x3^2+8064*x2*x4^2-10224*x3^3-1344*x3^2*x4+6768*x3^2*x5-170*x3*x4*x5+250*x4*x5^2+910*x5^3+1373*x1^2-284*x1*x3+558*x1*x5+625*x2^2+4800*x2*x4+5041*x3^2-6674*x3*x5+9216*x4^2+2234*x5^2, 21474*x1^2*x2-66*x1^2*x4+5616*x1*x3^2-3264*x1*x3*x4+9840*x1*x4*x5+17472*x1*x5^2+3528*x2*x4^2-588*x3^2*x4+4760*x1^2-5538*x1*x3+7626*x1*x5+4200*x2*x4-350*x3^2+8064*x4^2+1250*x2+4800*x4, 1400*x1^2*x3+11232*x1*x2*x3-3264*x1*x2*x4+15264*x1*x3*x4-1680*x1*x3*x5-1176*x2*x3*x4+20932*x3^3+578*x3*x4^2-850*x4^2*x5-3094*x4*x5^2-5538*x1*x2+576*x1*x3-8784*x1*x4-700*x2*x3-30672*x3^2-2688*x3*x4+13536*x3*x5-170*x4*x5-284*x1+10082*x3-6674*x5, -66*x1^2*x2+5618*x1^2*x4-3264*x1*x2*x3+9840*x1*x2*x5+7632*x1*x3^2+3528*x2^2*x4-588*x2*x3^2+578*x3^2*x4-1700*x3*x4*x5-3094*x3*x5^2+1250*x4*x5^2+4550*x5^3-9388*x1^2-8784*x1*x3+18352*x1*x5+2100*x2^2+16128*x2*x4-1344*x3^2-170*x3*x5+250*x5^2+4800*x2+18432*x4, -6000*x1^3+7200*x1^2*x5+9840*x1*x2*x4+34944*x1*x2*x5-840*x1*x3^2-850*x3*x4^2-6188*x3*x4*x5+1250*x4^2*x5+13650*x4*x5^2+33124*x5^3+7626*x1*x2+18352*x1*x4+13468*x1*x5+6768*x3^2-170*x3*x4+500*x4*x5+2730*x5^2+558*x1-6674*x3+4468*x5];
gb = SignatureGB.f5([2500*x1^4-6000*x1^3*x5+10737*x1^2*x2^2-66*x1^2*x2*x4+700*x1^2*x3^2+2809*x1^2*x4^2+3600*x1^2*x5^2+5616*x1*x2*x3^2-3264*x1*x2*x3*x4+9840*x1*x2*x4*x5+17472*x1*x2*x5^2+7632*x1*x3^2*x4-840*x1*x3^2*x5+1764*x2^2*x4^2-588*x2*x3^2*x4+5233*x3^4+289*x3^2*x4^2-850*x3*x4^2*x5-3094*x3*x4*x5^2+625*x4^2*x5^2+4550*x4*x5^3+8281*x5^4+4760*x1^2*x2-9388*x1^2*x4-5538*x1*x2*x3+7626*x1*x2*x5+288*x1*x3^2-8784*x1*x3*x4+18352*x1*x4*x5+6734*x1*x5^2+2100*x2^2*x4-350*x2*x3^2+8064*x2*x4^2-10224*x3^3-1344*x3^2*x4+6768*x3^2*x5-170*x3*x4*x5+250*x4*x5^2+910*x5^3+1373*x1^2-284*x1*x3+558*x1*x5+625*x2^2+4800*x2*x4+5041*x3^2-6674*x3*x5+9216*x4^2+2234*x5^2, 21474*x1^2*x2-66*x1^2*x4+5616*x1*x3^2-3264*x1*x3*x4+9840*x1*x4*x5+17472*x1*x5^2+3528*x2*x4^2-588*x3^2*x4+4760*x1^2-5538*x1*x3+7626*x1*x5+4200*x2*x4-350*x3^2+8064*x4^2+1250*x2+4800*x4, 1400*x1^2*x3+11232*x1*x2*x3-3264*x1*x2*x4+15264*x1*x3*x4-1680*x1*x3*x5-1176*x2*x3*x4+20932*x3^3+578*x3*x4^2-850*x4^2*x5-3094*x4*x5^2-5538*x1*x2+576*x1*x3-8784*x1*x4-700*x2*x3-30672*x3^2-2688*x3*x4+13536*x3*x5-170*x4*x5-284*x1+10082*x3-6674*x5, -66*x1^2*x2+5618*x1^2*x4-3264*x1*x2*x3+9840*x1*x2*x5+7632*x1*x3^2+3528*x2^2*x4-588*x2*x3^2+578*x3^2*x4-1700*x3*x4*x5-3094*x3*x5^2+1250*x4*x5^2+4550*x5^3-9388*x1^2-8784*x1*x3+18352*x1*x5+2100*x2^2+16128*x2*x4-1344*x3^2-170*x3*x5+250*x5^2+4800*x2+18432*x4, -6000*x1^3+7200*x1^2*x5+9840*x1*x2*x4+34944*x1*x2*x5-840*x1*x3^2-850*x3*x4^2-6188*x3*x4*x5+1250*x4^2*x5+13650*x4*x5^2+33124*x5^3+7626*x1*x2+18352*x1*x4+13468*x1*x5+6768*x3^2-170*x3*x4+500*x4*x5+2730*x5^2+558*x1-6674*x3+4468*x5], verbose=true);[leading_monomial(g) for g in gb];exit()
