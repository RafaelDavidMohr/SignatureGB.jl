using SignatureGB
using Singular
P, (x1, x2, x3, x4, x5, x6, x7)  = Singular.PolynomialRing(Fp(65521), ["x1", "x2", "x3", "x4", "x5", "x6", "x7"]);
gb = SignatureGB.f5([x1, x2, x3, x4, x5, x6, x7]);F = [3969*x1^4+10625*x1^2*x2^2-5304*x1^2*x2*x3-534*x1^2*x2*x5+8701*x1^2*x3^2-10008*x1^2*x3*x6-11214*x1^2*x3*x7+7056*x1^2*x4^2+6409*x1^2*x5^2+2601*x1^2*x6^2-9198*x1^2*x7^2+10520*x1*x2^2*x5+14240*x1*x2^2*x7-10386*x1*x2*x3^2-5886*x1*x2*x3*x5-3952*x1*x2*x3*x7-2392*x1*x2*x4*x7+4998*x1*x2*x5*x6+2328*x1*x2*x5*x7-1064*x1*x3^2*x4+14622*x1*x3^2*x5-12912*x1*x3*x4^2-2080*x1*x3*x4*x5+2346*x1*x3*x4*x7-2754*x1*x3*x5*x7-5472*x1*x3*x6*x7+3468*x1*x4^2*x6-10880*x1*x5^2*x7+13440*x1*x5*x6*x7+289*x2^4+3685*x2^2*x3^2-442*x2^2*x3*x4+1300*x2^2*x3*x7+8026*x2^2*x5^2-2312*x2^2*x5*x7+2856*x2^2*x6*x7+7076*x2^2*x7^2+350*x2*x3^2*x4-5920*x2*x3^2*x7+4650*x2*x3*x4^2+364*x2*x3*x4*x7+1800*x2*x3*x6*x7+3332*x2*x4^2*x5+4836*x2*x4^2*x7-3450*x2*x4*x5*x7+4050*x2*x5^2*x7+1872*x2*x6*x7^2+9469*x3^4-2340*x3^3*x4+218*x3^2*x4^2-12240*x3^2*x5*x7+8836*x3^2*x6^2+31852*x3^2*x6*x7+7921*x3^2*x7^2+1302*x3*x4^3-10528*x3*x4^2*x6-9968*x3*x4^2*x7+1768*x3*x4*x5*x7-1680*x3*x4*x6*x7+13724*x3*x6*x7^2+12994*x3*x7^3+12941*x4^4+6696*x4^2*x6*x7-7647*x4^2*x7^2-1242*x4*x5*x7^2+5353*x5^2*x7^2-11424*x5*x6*x7^2+8352*x6^2*x7^2+5329*x7^4+3026*x1^2*x2+7938*x1^2*x4-102*x1^2*x5-7654*x1*x2^2+936*x1*x2*x3+258*x1*x2*x5+2720*x1*x2*x7-2176*x1*x3^2-792*x1*x3*x4+2052*x1*x3*x6-2244*x1*x4*x6+5814*x1*x6^2-6880*x2^2*x7+3182*x2*x3^2+1350*x2*x3*x5-2156*x2*x4*x5+5586*x2*x5*x6-11844*x3*x4*x6-11628*x3*x4*x7+486*x3*x5*x7+5560*x4^3+3876*x4^2*x6-9198*x4*x7^2+289*x1^2-1462*x1*x2+1849*x2^2+81*x3^2+4453*x4^2-2508*x4*x6+3249*x6^2, 21250*x1^2*x2-5304*x1^2*x3-534*x1^2*x5+21040*x1*x2*x5+28480*x1*x2*x7-10386*x1*x3^2-5886*x1*x3*x5-3952*x1*x3*x7-2392*x1*x4*x7+4998*x1*x5*x6+2328*x1*x5*x7+1156*x2^3+7370*x2*x3^2-884*x2*x3*x4+2600*x2*x3*x7+16052*x2*x5^2-4624*x2*x5*x7+5712*x2*x6*x7+14152*x2*x7^2+350*x3^2*x4-5920*x3^2*x7+4650*x3*x4^2+364*x3*x4*x7+1800*x3*x6*x7+3332*x4^2*x5+4836*x4^2*x7-3450*x4*x5*x7+4050*x5^2*x7+1872*x6*x7^2+3026*x1^2-15308*x1*x2+936*x1*x3+258*x1*x5+2720*x1*x7-13760*x2*x7+3182*x3^2+1350*x3*x5-2156*x4*x5+5586*x5*x6-1462*x1+3698*x2, -5304*x1^2*x2+17402*x1^2*x3-10008*x1^2*x6-11214*x1^2*x7-20772*x1*x2*x3-5886*x1*x2*x5-3952*x1*x2*x7-2128*x1*x3*x4+29244*x1*x3*x5-12912*x1*x4^2-2080*x1*x4*x5+2346*x1*x4*x7-2754*x1*x5*x7-5472*x1*x6*x7+7370*x2^2*x3-442*x2^2*x4+1300*x2^2*x7+700*x2*x3*x4-11840*x2*x3*x7+4650*x2*x4^2+364*x2*x4*x7+1800*x2*x6*x7+37876*x3^3-7020*x3^2*x4+436*x3*x4^2-24480*x3*x5*x7+17672*x3*x6^2+63704*x3*x6*x7+15842*x3*x7^2+1302*x4^3-10528*x4^2*x6-9968*x4^2*x7+1768*x4*x5*x7-1680*x4*x6*x7+13724*x6*x7^2+12994*x7^3+936*x1*x2-4352*x1*x3-792*x1*x4+2052*x1*x6+6364*x2*x3+1350*x2*x5-11844*x4*x6-11628*x4*x7+486*x5*x7+162*x3, 14112*x1^2*x4-2392*x1*x2*x7-1064*x1*x3^2-25824*x1*x3*x4-2080*x1*x3*x5+2346*x1*x3*x7+6936*x1*x4*x6-442*x2^2*x3+350*x2*x3^2+9300*x2*x3*x4+364*x2*x3*x7+6664*x2*x4*x5+9672*x2*x4*x7-3450*x2*x5*x7-2340*x3^3+436*x3^2*x4+3906*x3*x4^2-21056*x3*x4*x6-19936*x3*x4*x7+1768*x3*x5*x7-1680*x3*x6*x7+51764*x4^3+13392*x4*x6*x7-15294*x4*x7^2-1242*x5*x7^2+7938*x1^2-792*x1*x3-2244*x1*x6-2156*x2*x5-11844*x3*x6-11628*x3*x7+16680*x4^2+7752*x4*x6-9198*x7^2+8906*x4-2508*x6, -534*x1^2*x2+12818*x1^2*x5+10520*x1*x2^2-5886*x1*x2*x3+4998*x1*x2*x6+2328*x1*x2*x7+14622*x1*x3^2-2080*x1*x3*x4-2754*x1*x3*x7-21760*x1*x5*x7+13440*x1*x6*x7+16052*x2^2*x5-2312*x2^2*x7+3332*x2*x4^2-3450*x2*x4*x7+8100*x2*x5*x7-12240*x3^2*x7+1768*x3*x4*x7-1242*x4*x7^2+10706*x5*x7^2-11424*x6*x7^2-102*x1^2+258*x1*x2+1350*x2*x3-2156*x2*x4+5586*x2*x6+486*x3*x7, -10008*x1^2*x3+5202*x1^2*x6+4998*x1*x2*x5-5472*x1*x3*x7+3468*x1*x4^2+13440*x1*x5*x7+2856*x2^2*x7+1800*x2*x3*x7+1872*x2*x7^2+17672*x3^2*x6+31852*x3^2*x7-10528*x3*x4^2-1680*x3*x4*x7+13724*x3*x7^2+6696*x4^2*x7-11424*x5*x7^2+16704*x6*x7^2+2052*x1*x3-2244*x1*x4+11628*x1*x6+5586*x2*x5-11844*x3*x4+3876*x4^2-2508*x4+6498*x6, -11214*x1^2*x3-18396*x1^2*x7+14240*x1*x2^2-3952*x1*x2*x3-2392*x1*x2*x4+2328*x1*x2*x5+2346*x1*x3*x4-2754*x1*x3*x5-5472*x1*x3*x6-10880*x1*x5^2+13440*x1*x5*x6+1300*x2^2*x3-2312*x2^2*x5+2856*x2^2*x6+14152*x2^2*x7-5920*x2*x3^2+364*x2*x3*x4+1800*x2*x3*x6+4836*x2*x4^2-3450*x2*x4*x5+4050*x2*x5^2+3744*x2*x6*x7-12240*x3^2*x5+31852*x3^2*x6+15842*x3^2*x7-9968*x3*x4^2+1768*x3*x4*x5-1680*x3*x4*x6+27448*x3*x6*x7+38982*x3*x7^2+6696*x4^2*x6-15294*x4^2*x7-2484*x4*x5*x7+10706*x5^2*x7-22848*x5*x6*x7+16704*x6^2*x7+21316*x7^3+2720*x1*x2-6880*x2^2-11628*x3*x4+486*x3*x5-18396*x4*x7];
sort!(F, by = p -> leading_monomial(p))
println(@elapsed SignatureGB.f5(F, verbose=true));exit()
