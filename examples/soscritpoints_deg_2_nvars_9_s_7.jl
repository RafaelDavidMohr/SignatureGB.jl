using SignatureGB
using Singular
P, (x1, x2, x3, x4, x5, x6, x7, x8, x9)  = Singular.PolynomialRing(Fp(65521), ["x1", "x2", "x3", "x4", "x5", "x6", "x7", "x8", "x9"]);
gb = SignatureGB.f5([x1, x2, x3, x4, x5, x6, x7, x8, x9]);F = [3844*x1^4+841*x1^2*x2^2+992*x1^2*x2*x6+2916*x1^2*x5^2+10044*x1^2*x5*x9+289*x1^2*x6^2+3968*x1^2*x6*x7-722*x1*x2^2*x6+3886*x1*x2*x3*x5+3596*x1*x2*x4*x8-4104*x1*x2*x5^2-4640*x1*x2*x5*x8+490*x1*x2*x5*x9-2924*x1*x2*x6*x7-6696*x1*x5*x6*x7+3564*x1*x5*x7^2+2268*x1*x5*x7*x8+782*x1*x6^2*x9+1836*x1*x6*x7*x8+324*x2^4-3096*x2^3*x7+1768*x2^2*x5^2-2508*x2^2*x5*x9+593*x2^2*x6^2+828*x2^2*x6*x9+7396*x2^2*x7^2+1944*x2^2*x7*x8+1089*x2^2*x9^2-3082*x2*x3*x5*x6-3528*x2*x3*x5*x8-2852*x2*x4*x6*x8+4712*x2*x5*x6*x7+3680*x2*x5*x6*x8+3734*x2*x5*x6*x9-2436*x2*x5*x7^2-1596*x2*x5*x7*x8-3492*x2*x5*x8^2+936*x2*x5*x8*x9+512*x2*x6^2*x7-8048*x2*x6*x7*x9-9288*x2*x7^2*x8+2178*x2*x7^2*x9+1386*x2*x7*x8*x9+4489*x3^2*x5^2+6561*x3^2*x7^2-4050*x3^2*x7*x9+9604*x3^2*x8^2+629*x3^2*x9^2+8308*x3*x4*x5*x8+88*x3*x4*x6*x9-10720*x3*x5^2*x8-7102*x3*x5^2*x9-316*x3*x6^2*x9+136*x3*x6*x7*x9-296*x3*x6*x8*x9-12312*x3*x7^3-392*x3*x7^2*x8+3800*x3*x7^2*x9+19012*x3*x8^3-5112*x3*x8^2*x9+484*x4^2*x6^2+3844*x4^2*x8^2-9920*x4*x5*x8^2-6572*x4*x5*x8*x9-3476*x4*x6^3+1496*x4*x6^2*x7-3256*x4*x6^2*x8-176*x4*x6*x8^2+6400*x5^2*x8^2+8480*x5^2*x8*x9+9370*x5^2*x9^2+5184*x5*x6*x7*x9+6241*x6^4-5372*x6^3*x7+11692*x6^3*x8+6024*x6^2*x7^2-5032*x6^2*x7*x8+6108*x6^2*x8^2+529*x6^2*x9^2-4092*x6*x7^3-2604*x6*x7^2*x8-272*x6*x7*x8^2+2484*x6*x7*x8*x9+592*x6*x8^3+6869*x7^4+1386*x7^3*x8+2969*x7^2*x8^2+104*x7^2*x8*x9+9425*x8^4-5044*x8^3*x9+676*x8^2*x9^2+2108*x1^2*x8-2520*x1*x2*x5-2040*x1*x2*x6+13720*x1*x3*x8-280*x1*x7^2+13580*x1*x8^2-3640*x1*x8*x9-2160*x2^3+10320*x2^2*x7+272*x2*x6*x8-2760*x2*x6*x9-6480*x2*x7*x8+9072*x3*x4*x7-2800*x3*x4*x9-9234*x3*x7^2-4536*x3*x7*x8+2850*x3*x7*x9+1400*x3*x8*x9-8512*x4*x7^2+2754*x5*x8*x9+1088*x6*x7*x8+8664*x7^3+4256*x7^2*x8+16308*x1^2+3600*x2^2+1472*x2*x6+3136*x4^2-6384*x4*x7-3136*x4*x8+14904*x5*x9+5888*x6*x7+3249*x7^2+3192*x7*x8+1073*x8^2+3128*x8+8464, 1682*x1^2*x2+992*x1^2*x6-1444*x1*x2*x6+3886*x1*x3*x5+3596*x1*x4*x8-4104*x1*x5^2-4640*x1*x5*x8+490*x1*x5*x9-2924*x1*x6*x7+1296*x2^3-9288*x2^2*x7+3536*x2*x5^2-5016*x2*x5*x9+1186*x2*x6^2+1656*x2*x6*x9+14792*x2*x7^2+3888*x2*x7*x8+2178*x2*x9^2-3082*x3*x5*x6-3528*x3*x5*x8-2852*x4*x6*x8+4712*x5*x6*x7+3680*x5*x6*x8+3734*x5*x6*x9-2436*x5*x7^2-1596*x5*x7*x8-3492*x5*x8^2+936*x5*x8*x9+512*x6^2*x7-8048*x6*x7*x9-9288*x7^2*x8+2178*x7^2*x9+1386*x7*x8*x9-2520*x1*x5-2040*x1*x6-6480*x2^2+20640*x2*x7+272*x6*x8-2760*x6*x9-6480*x7*x8+7200*x2+1472*x6, 3886*x1*x2*x5-3082*x2*x5*x6-3528*x2*x5*x8+8978*x3*x5^2+13122*x3*x7^2-8100*x3*x7*x9+19208*x3*x8^2+1258*x3*x9^2+8308*x4*x5*x8+88*x4*x6*x9-10720*x5^2*x8-7102*x5^2*x9-316*x6^2*x9+136*x6*x7*x9-296*x6*x8*x9-12312*x7^3-392*x7^2*x8+3800*x7^2*x9+19012*x8^3-5112*x8^2*x9+13720*x1*x8+9072*x4*x7-2800*x4*x9-9234*x7^2-4536*x7*x8+2850*x7*x9+1400*x8*x9, 3596*x1*x2*x8-2852*x2*x6*x8+8308*x3*x5*x8+88*x3*x6*x9+968*x4*x6^2+7688*x4*x8^2-9920*x5*x8^2-6572*x5*x8*x9-3476*x6^3+1496*x6^2*x7-3256*x6^2*x8-176*x6*x8^2+9072*x3*x7-2800*x3*x9-8512*x7^2+6272*x4-6384*x7-3136*x8, 5832*x1^2*x5+10044*x1^2*x9+3886*x1*x2*x3-8208*x1*x2*x5-4640*x1*x2*x8+490*x1*x2*x9-6696*x1*x6*x7+3564*x1*x7^2+2268*x1*x7*x8+3536*x2^2*x5-2508*x2^2*x9-3082*x2*x3*x6-3528*x2*x3*x8+4712*x2*x6*x7+3680*x2*x6*x8+3734*x2*x6*x9-2436*x2*x7^2-1596*x2*x7*x8-3492*x2*x8^2+936*x2*x8*x9+8978*x3^2*x5+8308*x3*x4*x8-21440*x3*x5*x8-14204*x3*x5*x9-9920*x4*x8^2-6572*x4*x8*x9+12800*x5*x8^2+16960*x5*x8*x9+18740*x5*x9^2+5184*x6*x7*x9-2520*x1*x2+2754*x8*x9+14904*x9, 992*x1^2*x2+578*x1^2*x6+3968*x1^2*x7-722*x1*x2^2-2924*x1*x2*x7-6696*x1*x5*x7+1564*x1*x6*x9+1836*x1*x7*x8+1186*x2^2*x6+828*x2^2*x9-3082*x2*x3*x5-2852*x2*x4*x8+4712*x2*x5*x7+3680*x2*x5*x8+3734*x2*x5*x9+1024*x2*x6*x7-8048*x2*x7*x9+88*x3*x4*x9-632*x3*x6*x9+136*x3*x7*x9-296*x3*x8*x9+968*x4^2*x6-10428*x4*x6^2+2992*x4*x6*x7-6512*x4*x6*x8-176*x4*x8^2+5184*x5*x7*x9+24964*x6^3-16116*x6^2*x7+35076*x6^2*x8+12048*x6*x7^2-10064*x6*x7*x8+12216*x6*x8^2+1058*x6*x9^2-4092*x7^3-2604*x7^2*x8-272*x7*x8^2+2484*x7*x8*x9+592*x8^3-2040*x1*x2+272*x2*x8-2760*x2*x9+1088*x7*x8+1472*x2+5888*x7, 3968*x1^2*x6-2924*x1*x2*x6-6696*x1*x5*x6+7128*x1*x5*x7+2268*x1*x5*x8+1836*x1*x6*x8-3096*x2^3+14792*x2^2*x7+1944*x2^2*x8+4712*x2*x5*x6-4872*x2*x5*x7-1596*x2*x5*x8+512*x2*x6^2-8048*x2*x6*x9-18576*x2*x7*x8+4356*x2*x7*x9+1386*x2*x8*x9+13122*x3^2*x7-4050*x3^2*x9+136*x3*x6*x9-36936*x3*x7^2-784*x3*x7*x8+7600*x3*x7*x9+1496*x4*x6^2+5184*x5*x6*x9-5372*x6^3+12048*x6^2*x7-5032*x6^2*x8-12276*x6*x7^2-5208*x6*x7*x8-272*x6*x8^2+2484*x6*x8*x9+27476*x7^3+4158*x7^2*x8+5938*x7*x8^2+208*x7*x8*x9-560*x1*x7+10320*x2^2-6480*x2*x8+9072*x3*x4-18468*x3*x7-4536*x3*x8+2850*x3*x9-17024*x4*x7+1088*x6*x8+25992*x7^2+8512*x7*x8-6384*x4+5888*x6+6498*x7+3192*x8, 3596*x1*x2*x4-4640*x1*x2*x5+2268*x1*x5*x7+1836*x1*x6*x7+1944*x2^2*x7-3528*x2*x3*x5-2852*x2*x4*x6+3680*x2*x5*x6-1596*x2*x5*x7-6984*x2*x5*x8+936*x2*x5*x9-9288*x2*x7^2+1386*x2*x7*x9+19208*x3^2*x8+8308*x3*x4*x5-10720*x3*x5^2-296*x3*x6*x9-392*x3*x7^2+57036*x3*x8^2-10224*x3*x8*x9+7688*x4^2*x8-19840*x4*x5*x8-6572*x4*x5*x9-3256*x4*x6^2-352*x4*x6*x8+12800*x5^2*x8+8480*x5^2*x9+11692*x6^3-5032*x6^2*x7+12216*x6^2*x8-2604*x6*x7^2-544*x6*x7*x8+2484*x6*x7*x9+1776*x6*x8^2+1386*x7^3+5938*x7^2*x8+104*x7^2*x9+37700*x8^3-15132*x8^2*x9+1352*x8*x9^2+2108*x1^2+13720*x1*x3+27160*x1*x8-3640*x1*x9+272*x2*x6-6480*x2*x7-4536*x3*x7+1400*x3*x9+2754*x5*x9+1088*x6*x7+4256*x7^2-3136*x4+3192*x7+2146*x8+3128, 10044*x1^2*x5+490*x1*x2*x5+782*x1*x6^2-2508*x2^2*x5+828*x2^2*x6+2178*x2^2*x9+3734*x2*x5*x6+936*x2*x5*x8-8048*x2*x6*x7+2178*x2*x7^2+1386*x2*x7*x8-4050*x3^2*x7+1258*x3^2*x9+88*x3*x4*x6-7102*x3*x5^2-316*x3*x6^2+136*x3*x6*x7-296*x3*x6*x8+3800*x3*x7^2-5112*x3*x8^2-6572*x4*x5*x8+8480*x5^2*x8+18740*x5^2*x9+5184*x5*x6*x7+1058*x6^2*x9+2484*x6*x7*x8+104*x7^2*x8-5044*x8^3+1352*x8^2*x9-3640*x1*x8-2760*x2*x6-2800*x3*x4+2850*x3*x7+1400*x3*x8+2754*x5*x8+14904*x5];
sort!(F, by = p -> leading_monomial(p))
println(@elapsed SignatureGB.f5(F, verbose=true));exit()
