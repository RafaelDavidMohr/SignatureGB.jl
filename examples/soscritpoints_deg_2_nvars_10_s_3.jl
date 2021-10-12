using SignatureGB
using Singular
P, (x1, x2, x3, x4, x5, x6, x7, x8, x9, x10)  = Singular.PolynomialRing(Fp(65521), ["x1", "x2", "x3", "x4", "x5", "x6", "x7", "x8", "x9", "x10"]);
gb = SignatureGB.f5([x1, x2, x3, x4, x5, x6, x7, x8, x9, x10]);F = [7921*x1^4+3382*x1^3*x2+8649*x1^2*x10^2+4094*x1^2*x10*x5+13172*x1^2*x10*x7+13578*x1^2*x10*x8+361*x1^2*x2^2+17266*x1^2*x4^2+12460*x1^2*x4*x7+5329*x1^2*x8^2+13020*x1*x10^3+10220*x1*x10^2*x8+874*x1*x10*x2*x5+2812*x1*x10*x2*x7-558*x1*x10*x3^2-5022*x1*x10*x6*x8+10416*x1*x10*x7*x9+3686*x1*x2*x4^2+2660*x1*x2*x4*x7-438*x1*x3^2*x8-3942*x1*x6*x8^2+8176*x1*x7*x8*x9+4936*x10^4-840*x10^3*x5-372*x10^3*x8-588*x10^2*x2^2-420*x10^2*x3^2+1104*x10^2*x4*x9+5429*x10^2*x5^2+3404*x10^2*x5*x7+4340*x10^2*x5*x8-3780*x10^2*x6*x8+5476*x10^2*x7^2+7840*x10^2*x7*x9+961*x10^2*x8^2+6860*x10*x2^2*x5+3038*x10*x2^2*x8+4462*x10*x4^2*x5+14356*x10*x4^2*x7+3220*x10*x4*x5*x7-12880*x10*x4*x5*x9+10360*x10*x4*x7^2-5704*x10*x4*x8*x9+2401*x2^4-9016*x2^2*x4*x9+9*x3^4+162*x3^2*x6*x8-336*x3^2*x7*x9+9409*x4^4+13580*x4^3*x7+4900*x4^2*x7^2+8464*x4^2*x9^2+729*x6^2*x8^2-3024*x6*x7*x8*x9+3136*x7^2*x9^2-564*x1*x10^2+6580*x1*x10*x5+2914*x1*x10*x8+4606*x1*x2^2-8648*x1*x4*x9+2209*x1^2, 3382*x1^3+722*x1^2*x2+874*x1*x10*x5+2812*x1*x10*x7+3686*x1*x4^2+2660*x1*x4*x7-1176*x10^2*x2+13720*x10*x2*x5+6076*x10*x2*x8+9604*x2^3-18032*x2*x4*x9+9212*x1*x2, -1116*x1*x10*x3-876*x1*x3*x8-840*x10^2*x3+36*x3^3+324*x3*x6*x8-672*x3*x7*x9, 34532*x1^2*x4+12460*x1^2*x7+7372*x1*x2*x4+2660*x1*x2*x7+1104*x10^2*x9+8924*x10*x4*x5+28712*x10*x4*x7+3220*x10*x5*x7-12880*x10*x5*x9+10360*x10*x7^2-5704*x10*x8*x9-9016*x2^2*x9+37636*x4^3+40740*x4^2*x7+9800*x4*x7^2+16928*x4*x9^2-8648*x1*x9, 4094*x1^2*x10+874*x1*x10*x2-840*x10^3+10858*x10^2*x5+3404*x10^2*x7+4340*x10^2*x8+6860*x10*x2^2+4462*x10*x4^2+3220*x10*x4*x7-12880*x10*x4*x9+6580*x1*x10, -5022*x1*x10*x8-3942*x1*x8^2-3780*x10^2*x8+162*x3^2*x8+1458*x6*x8^2-3024*x7*x8*x9, 13172*x1^2*x10+12460*x1^2*x4+2812*x1*x10*x2+10416*x1*x10*x9+2660*x1*x2*x4+8176*x1*x8*x9+3404*x10^2*x5+10952*x10^2*x7+7840*x10^2*x9+14356*x10*x4^2+3220*x10*x4*x5+20720*x10*x4*x7-336*x3^2*x9+13580*x4^3+9800*x4^2*x7-3024*x6*x8*x9+6272*x7*x9^2, 13578*x1^2*x10+10658*x1^2*x8+10220*x1*x10^2-5022*x1*x10*x6-438*x1*x3^2-7884*x1*x6*x8+8176*x1*x7*x9-372*x10^3+4340*x10^2*x5-3780*x10^2*x6+1922*x10^2*x8+3038*x10*x2^2-5704*x10*x4*x9+162*x3^2*x6+1458*x6^2*x8-3024*x6*x7*x9+2914*x1*x10, 10416*x1*x10*x7+8176*x1*x7*x8+1104*x10^2*x4+7840*x10^2*x7-12880*x10*x4*x5-5704*x10*x4*x8-9016*x2^2*x4-336*x3^2*x7+16928*x4^2*x9-3024*x6*x7*x8+6272*x7^2*x9-8648*x1*x4, 17298*x1^2*x10+4094*x1^2*x5+13172*x1^2*x7+13578*x1^2*x8+39060*x1*x10^2+20440*x1*x10*x8+874*x1*x2*x5+2812*x1*x2*x7-558*x1*x3^2-5022*x1*x6*x8+10416*x1*x7*x9+19744*x10^3-2520*x10^2*x5-1116*x10^2*x8-1176*x10*x2^2-840*x10*x3^2+2208*x10*x4*x9+10858*x10*x5^2+6808*x10*x5*x7+8680*x10*x5*x8-7560*x10*x6*x8+10952*x10*x7^2+15680*x10*x7*x9+1922*x10*x8^2+6860*x2^2*x5+3038*x2^2*x8+4462*x4^2*x5+14356*x4^2*x7+3220*x4*x5*x7-12880*x4*x5*x9+10360*x4*x7^2-5704*x4*x8*x9-1128*x1*x10+6580*x1*x5+2914*x1*x8];
gb = SignatureGB.f5([7921*x1^4+3382*x1^3*x2+8649*x1^2*x10^2+4094*x1^2*x10*x5+13172*x1^2*x10*x7+13578*x1^2*x10*x8+361*x1^2*x2^2+17266*x1^2*x4^2+12460*x1^2*x4*x7+5329*x1^2*x8^2+13020*x1*x10^3+10220*x1*x10^2*x8+874*x1*x10*x2*x5+2812*x1*x10*x2*x7-558*x1*x10*x3^2-5022*x1*x10*x6*x8+10416*x1*x10*x7*x9+3686*x1*x2*x4^2+2660*x1*x2*x4*x7-438*x1*x3^2*x8-3942*x1*x6*x8^2+8176*x1*x7*x8*x9+4936*x10^4-840*x10^3*x5-372*x10^3*x8-588*x10^2*x2^2-420*x10^2*x3^2+1104*x10^2*x4*x9+5429*x10^2*x5^2+3404*x10^2*x5*x7+4340*x10^2*x5*x8-3780*x10^2*x6*x8+5476*x10^2*x7^2+7840*x10^2*x7*x9+961*x10^2*x8^2+6860*x10*x2^2*x5+3038*x10*x2^2*x8+4462*x10*x4^2*x5+14356*x10*x4^2*x7+3220*x10*x4*x5*x7-12880*x10*x4*x5*x9+10360*x10*x4*x7^2-5704*x10*x4*x8*x9+2401*x2^4-9016*x2^2*x4*x9+9*x3^4+162*x3^2*x6*x8-336*x3^2*x7*x9+9409*x4^4+13580*x4^3*x7+4900*x4^2*x7^2+8464*x4^2*x9^2+729*x6^2*x8^2-3024*x6*x7*x8*x9+3136*x7^2*x9^2-564*x1*x10^2+6580*x1*x10*x5+2914*x1*x10*x8+4606*x1*x2^2-8648*x1*x4*x9+2209*x1^2, 3382*x1^3+722*x1^2*x2+874*x1*x10*x5+2812*x1*x10*x7+3686*x1*x4^2+2660*x1*x4*x7-1176*x10^2*x2+13720*x10*x2*x5+6076*x10*x2*x8+9604*x2^3-18032*x2*x4*x9+9212*x1*x2, -1116*x1*x10*x3-876*x1*x3*x8-840*x10^2*x3+36*x3^3+324*x3*x6*x8-672*x3*x7*x9, 34532*x1^2*x4+12460*x1^2*x7+7372*x1*x2*x4+2660*x1*x2*x7+1104*x10^2*x9+8924*x10*x4*x5+28712*x10*x4*x7+3220*x10*x5*x7-12880*x10*x5*x9+10360*x10*x7^2-5704*x10*x8*x9-9016*x2^2*x9+37636*x4^3+40740*x4^2*x7+9800*x4*x7^2+16928*x4*x9^2-8648*x1*x9, 4094*x1^2*x10+874*x1*x10*x2-840*x10^3+10858*x10^2*x5+3404*x10^2*x7+4340*x10^2*x8+6860*x10*x2^2+4462*x10*x4^2+3220*x10*x4*x7-12880*x10*x4*x9+6580*x1*x10, -5022*x1*x10*x8-3942*x1*x8^2-3780*x10^2*x8+162*x3^2*x8+1458*x6*x8^2-3024*x7*x8*x9, 13172*x1^2*x10+12460*x1^2*x4+2812*x1*x10*x2+10416*x1*x10*x9+2660*x1*x2*x4+8176*x1*x8*x9+3404*x10^2*x5+10952*x10^2*x7+7840*x10^2*x9+14356*x10*x4^2+3220*x10*x4*x5+20720*x10*x4*x7-336*x3^2*x9+13580*x4^3+9800*x4^2*x7-3024*x6*x8*x9+6272*x7*x9^2, 13578*x1^2*x10+10658*x1^2*x8+10220*x1*x10^2-5022*x1*x10*x6-438*x1*x3^2-7884*x1*x6*x8+8176*x1*x7*x9-372*x10^3+4340*x10^2*x5-3780*x10^2*x6+1922*x10^2*x8+3038*x10*x2^2-5704*x10*x4*x9+162*x3^2*x6+1458*x6^2*x8-3024*x6*x7*x9+2914*x1*x10, 10416*x1*x10*x7+8176*x1*x7*x8+1104*x10^2*x4+7840*x10^2*x7-12880*x10*x4*x5-5704*x10*x4*x8-9016*x2^2*x4-336*x3^2*x7+16928*x4^2*x9-3024*x6*x7*x8+6272*x7^2*x9-8648*x1*x4, 17298*x1^2*x10+4094*x1^2*x5+13172*x1^2*x7+13578*x1^2*x8+39060*x1*x10^2+20440*x1*x10*x8+874*x1*x2*x5+2812*x1*x2*x7-558*x1*x3^2-5022*x1*x6*x8+10416*x1*x7*x9+19744*x10^3-2520*x10^2*x5-1116*x10^2*x8-1176*x10*x2^2-840*x10*x3^2+2208*x10*x4*x9+10858*x10*x5^2+6808*x10*x5*x7+8680*x10*x5*x8-7560*x10*x6*x8+10952*x10*x7^2+15680*x10*x7*x9+1922*x10*x8^2+6860*x2^2*x5+3038*x2^2*x8+4462*x4^2*x5+14356*x4^2*x7+3220*x4*x5*x7-12880*x4*x5*x9+10360*x4*x7^2-5704*x4*x8*x9-1128*x1*x10+6580*x1*x5+2914*x1*x8], verbose=true);[leading_monomial(g) for g in gb];exit()