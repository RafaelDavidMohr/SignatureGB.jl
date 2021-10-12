using SignatureGB
using Singular
P, (x1, x2, x3, x4, x5, x6, x7)  = Singular.PolynomialRing(Fp(65521), ["x1", "x2", "x3", "x4", "x5", "x6", "x7"]);
gb = SignatureGB.f5([x1, x2, x3, x4, x5, x6, x7]);F = [484*x1^4+2420*x1^2*x2*x4+1496*x1^2*x2*x7-2288*x1^2*x3*x5-44*x1^2*x5*x7-3828*x1^2*x6*x7+3025*x2^2*x4^2+3740*x2^2*x4*x7+9025*x2^2*x6^2+12350*x2^2*x6*x7+5381*x2^2*x7^2-5720*x2*x3*x4*x5-3536*x2*x3*x5*x7-1900*x2*x3*x6^2-1300*x2*x3*x6*x7-110*x2*x4*x5*x7-7480*x2*x4*x6*x7+1430*x2*x4*x7^2-10640*x2*x5*x6*x7-7348*x2*x5*x7^2-5916*x2*x6*x7^2+2704*x3^2*x5^2+100*x3^2*x6^2-220*x3*x4*x6*x7+104*x3*x5^2*x7+10168*x3*x5*x6*x7+121*x4^2*x7^2-1232*x4*x5*x7^2+3137*x5^2*x7^2+174*x5*x6*x7^2+7569*x6^2*x7^2+14060*x2*x6+9620*x2*x7-1480*x3*x6+1628*x4*x7-8288*x5*x7+5476, 2420*x1^2*x4+1496*x1^2*x7+6050*x2*x4^2+7480*x2*x4*x7+18050*x2*x6^2+24700*x2*x6*x7+10762*x2*x7^2-5720*x3*x4*x5-3536*x3*x5*x7-1900*x3*x6^2-1300*x3*x6*x7-110*x4*x5*x7-7480*x4*x6*x7+1430*x4*x7^2-10640*x5*x6*x7-7348*x5*x7^2-5916*x6*x7^2+14060*x6+9620*x7, -2288*x1^2*x5-5720*x2*x4*x5-3536*x2*x5*x7-1900*x2*x6^2-1300*x2*x6*x7+5408*x3*x5^2+200*x3*x6^2-220*x4*x6*x7+104*x5^2*x7+10168*x5*x6*x7-1480*x6, 2420*x1^2*x2+6050*x2^2*x4+3740*x2^2*x7-5720*x2*x3*x5-110*x2*x5*x7-7480*x2*x6*x7+1430*x2*x7^2-220*x3*x6*x7+242*x4*x7^2-1232*x5*x7^2+1628*x7, -2288*x1^2*x3-44*x1^2*x7-5720*x2*x3*x4-3536*x2*x3*x7-110*x2*x4*x7-10640*x2*x6*x7-7348*x2*x7^2+5408*x3^2*x5+208*x3*x5*x7+10168*x3*x6*x7-1232*x4*x7^2+6274*x5*x7^2+174*x6*x7^2-8288*x7, -3828*x1^2*x7+18050*x2^2*x6+12350*x2^2*x7-3800*x2*x3*x6-1300*x2*x3*x7-7480*x2*x4*x7-10640*x2*x5*x7-5916*x2*x7^2+200*x3^2*x6-220*x3*x4*x7+10168*x3*x5*x7+174*x5*x7^2+15138*x6*x7^2+14060*x2-1480*x3, 1496*x1^2*x2-44*x1^2*x5-3828*x1^2*x6+3740*x2^2*x4+12350*x2^2*x6+10762*x2^2*x7-3536*x2*x3*x5-1300*x2*x3*x6-110*x2*x4*x5-7480*x2*x4*x6+2860*x2*x4*x7-10640*x2*x5*x6-14696*x2*x5*x7-11832*x2*x6*x7-220*x3*x4*x6+104*x3*x5^2+10168*x3*x5*x6+242*x4^2*x7-2464*x4*x5*x7+6274*x5^2*x7+348*x5*x6*x7+15138*x6^2*x7+9620*x2+1628*x4-8288*x5];
gb = SignatureGB.f5([484*x1^4+2420*x1^2*x2*x4+1496*x1^2*x2*x7-2288*x1^2*x3*x5-44*x1^2*x5*x7-3828*x1^2*x6*x7+3025*x2^2*x4^2+3740*x2^2*x4*x7+9025*x2^2*x6^2+12350*x2^2*x6*x7+5381*x2^2*x7^2-5720*x2*x3*x4*x5-3536*x2*x3*x5*x7-1900*x2*x3*x6^2-1300*x2*x3*x6*x7-110*x2*x4*x5*x7-7480*x2*x4*x6*x7+1430*x2*x4*x7^2-10640*x2*x5*x6*x7-7348*x2*x5*x7^2-5916*x2*x6*x7^2+2704*x3^2*x5^2+100*x3^2*x6^2-220*x3*x4*x6*x7+104*x3*x5^2*x7+10168*x3*x5*x6*x7+121*x4^2*x7^2-1232*x4*x5*x7^2+3137*x5^2*x7^2+174*x5*x6*x7^2+7569*x6^2*x7^2+14060*x2*x6+9620*x2*x7-1480*x3*x6+1628*x4*x7-8288*x5*x7+5476, 2420*x1^2*x4+1496*x1^2*x7+6050*x2*x4^2+7480*x2*x4*x7+18050*x2*x6^2+24700*x2*x6*x7+10762*x2*x7^2-5720*x3*x4*x5-3536*x3*x5*x7-1900*x3*x6^2-1300*x3*x6*x7-110*x4*x5*x7-7480*x4*x6*x7+1430*x4*x7^2-10640*x5*x6*x7-7348*x5*x7^2-5916*x6*x7^2+14060*x6+9620*x7, -2288*x1^2*x5-5720*x2*x4*x5-3536*x2*x5*x7-1900*x2*x6^2-1300*x2*x6*x7+5408*x3*x5^2+200*x3*x6^2-220*x4*x6*x7+104*x5^2*x7+10168*x5*x6*x7-1480*x6, 2420*x1^2*x2+6050*x2^2*x4+3740*x2^2*x7-5720*x2*x3*x5-110*x2*x5*x7-7480*x2*x6*x7+1430*x2*x7^2-220*x3*x6*x7+242*x4*x7^2-1232*x5*x7^2+1628*x7, -2288*x1^2*x3-44*x1^2*x7-5720*x2*x3*x4-3536*x2*x3*x7-110*x2*x4*x7-10640*x2*x6*x7-7348*x2*x7^2+5408*x3^2*x5+208*x3*x5*x7+10168*x3*x6*x7-1232*x4*x7^2+6274*x5*x7^2+174*x6*x7^2-8288*x7, -3828*x1^2*x7+18050*x2^2*x6+12350*x2^2*x7-3800*x2*x3*x6-1300*x2*x3*x7-7480*x2*x4*x7-10640*x2*x5*x7-5916*x2*x7^2+200*x3^2*x6-220*x3*x4*x7+10168*x3*x5*x7+174*x5*x7^2+15138*x6*x7^2+14060*x2-1480*x3, 1496*x1^2*x2-44*x1^2*x5-3828*x1^2*x6+3740*x2^2*x4+12350*x2^2*x6+10762*x2^2*x7-3536*x2*x3*x5-1300*x2*x3*x6-110*x2*x4*x5-7480*x2*x4*x6+2860*x2*x4*x7-10640*x2*x5*x6-14696*x2*x5*x7-11832*x2*x6*x7-220*x3*x4*x6+104*x3*x5^2+10168*x3*x5*x6+242*x4^2*x7-2464*x4*x5*x7+6274*x5^2*x7+348*x5*x6*x7+15138*x6^2*x7+9620*x2+1628*x4-8288*x5], verbose=true);[leading_monomial(g) for g in gb];exit()