using SignatureGB
using Singular
P, (x1, x2, x3, x4, x5, x6, x7, x8)  = Singular.PolynomialRing(Fp(65521), ["x1", "x2", "x3", "x4", "x5", "x6", "x7", "x8"]);
gb = SignatureGB.f5([x1, x2, x3, x4, x5, x6, x7, x8]);F = [6724*x1^2*x3^2+2916*x1^2*x5^2+9072*x1^2*x5*x6+7056*x1^2*x6^2+1600*x1^2*x8^2-1440*x1*x2^2*x8+13448*x1*x2*x3*x4-5724*x1*x2*x4*x5-8904*x1*x2*x4*x6-5120*x1*x2*x5*x8-4800*x1*x2*x6*x8+11316*x1*x3^2*x4+7020*x1*x3^2*x5+10920*x1*x3^2*x6-972*x1*x3*x5*x6-492*x1*x3*x5*x8-12828*x1*x3*x6^2-6400*x1*x8^3+324*x2^4+2304*x2^3*x5+2160*x2^3*x6+9533*x2^2*x4^2+4096*x2^2*x5^2+7680*x2^2*x5*x6+3616*x2^2*x6^2+296*x2^2*x6*x8+4249*x2^2*x8^2-6890*x2*x3^2*x4+11316*x2*x3*x4^2+954*x2*x3*x4*x6-492*x2*x4*x5*x8-11316*x2*x4*x6^2+272*x2*x5*x6*x8+12756*x2*x5*x8^2+9600*x2*x6*x8^2+4225*x3^4-1170*x3^3*x6+4761*x3^2*x4^2+81*x3^2*x6^2-414*x3*x4*x5*x8-9522*x3*x4*x6^2+1165*x5^2*x8^2+414*x5*x6^2*x8+4761*x6^4+6400*x8^4-152*x1*x2*x6-1406*x1*x2*x8+7668*x1*x5*x7+5108*x1*x5*x8+11928*x1*x6*x7-2880*x2^2*x5+256*x2^2*x6+2368*x2^2*x8-632*x2*x4*x6-7526*x2*x4*x7-5846*x2*x4*x8-10240*x2*x5^2-9600*x2*x5*x6+2176*x2*x5*x8+9230*x3^2*x7-1278*x3*x6*x7-5372*x4*x5*x8-12800*x5*x8^2+361*x1^2-1216*x1*x2+6560*x1*x3+3002*x1*x4+1024*x2^2+1504*x2*x4+5520*x3*x4+6241*x4^2+6400*x5^2-240*x5*x8-5520*x6^2+5041*x7^2+1600, -2880*x1*x2*x8+13448*x1*x3*x4-5724*x1*x4*x5-8904*x1*x4*x6-5120*x1*x5*x8-4800*x1*x6*x8+1296*x2^3+6912*x2^2*x5+6480*x2^2*x6+19066*x2*x4^2+8192*x2*x5^2+15360*x2*x5*x6+7232*x2*x6^2+592*x2*x6*x8+8498*x2*x8^2-6890*x3^2*x4+11316*x3*x4^2+954*x3*x4*x6-492*x4*x5*x8-11316*x4*x6^2+272*x5*x6*x8+12756*x5*x8^2+9600*x6*x8^2-152*x1*x6-1406*x1*x8-5760*x2*x5+512*x2*x6+4736*x2*x8-632*x4*x6-7526*x4*x7-5846*x4*x8-10240*x5^2-9600*x5*x6+2176*x5*x8-1216*x1+2048*x2+1504*x4, 13448*x1^2*x3+13448*x1*x2*x4+22632*x1*x3*x4+14040*x1*x3*x5+21840*x1*x3*x6-972*x1*x5*x6-492*x1*x5*x8-12828*x1*x6^2-13780*x2*x3*x4+11316*x2*x4^2+954*x2*x4*x6+16900*x3^3-3510*x3^2*x6+9522*x3*x4^2+162*x3*x6^2-414*x4*x5*x8-9522*x4*x6^2+18460*x3*x7-1278*x6*x7+6560*x1+5520*x4, 13448*x1*x2*x3-5724*x1*x2*x5-8904*x1*x2*x6+11316*x1*x3^2+19066*x2^2*x4-6890*x2*x3^2+22632*x2*x3*x4+954*x2*x3*x6-492*x2*x5*x8-11316*x2*x6^2+9522*x3^2*x4-414*x3*x5*x8-9522*x3*x6^2-632*x2*x6-7526*x2*x7-5846*x2*x8-5372*x5*x8+3002*x1+1504*x2+5520*x3+12482*x4, 5832*x1^2*x5+9072*x1^2*x6-5724*x1*x2*x4-5120*x1*x2*x8+7020*x1*x3^2-972*x1*x3*x6-492*x1*x3*x8+2304*x2^3+8192*x2^2*x5+7680*x2^2*x6-492*x2*x4*x8+272*x2*x6*x8+12756*x2*x8^2-414*x3*x4*x8+2330*x5*x8^2+414*x6^2*x8+7668*x1*x7+5108*x1*x8-2880*x2^2-20480*x2*x5-9600*x2*x6+2176*x2*x8-5372*x4*x8-12800*x8^2+12800*x5-240*x8, 9072*x1^2*x5+14112*x1^2*x6-8904*x1*x2*x4-4800*x1*x2*x8+10920*x1*x3^2-972*x1*x3*x5-25656*x1*x3*x6+2160*x2^3+7680*x2^2*x5+7232*x2^2*x6+296*x2^2*x8+954*x2*x3*x4-22632*x2*x4*x6+272*x2*x5*x8+9600*x2*x8^2-1170*x3^3+162*x3^2*x6-19044*x3*x4*x6+828*x5*x6*x8+19044*x6^3-152*x1*x2+11928*x1*x7+256*x2^2-632*x2*x4-9600*x2*x5-1278*x3*x7-11040*x6, 7668*x1*x5+11928*x1*x6-7526*x2*x4+9230*x3^2-1278*x3*x6+10082*x7, 3200*x1^2*x8-1440*x1*x2^2-5120*x1*x2*x5-4800*x1*x2*x6-492*x1*x3*x5-19200*x1*x8^2+296*x2^2*x6+8498*x2^2*x8-492*x2*x4*x5+272*x2*x5*x6+25512*x2*x5*x8+19200*x2*x6*x8-414*x3*x4*x5+2330*x5^2*x8+414*x5*x6^2+25600*x8^3-1406*x1*x2+5108*x1*x5+2368*x2^2-5846*x2*x4+2176*x2*x5-5372*x4*x5-25600*x5*x8-240*x5];
sort!(F, by = p -> leading_monomial(p))
println(@elapsed SignatureGB.f5(F, verbose=true));exit()
