using SignatureGB
using Singular
P, (x1, x2, x3, x4)  = Singular.PolynomialRing(Fp(65521), ["x1", "x2", "x3", "x4"]);
gb = SignatureGB.f5([x1, x2, x3, x4]);F = [841*x1^4-5510*x1^3*x2+9025*x1^2*x2^2-638*x1^2*x2*x3+2843*x1^2*x3^2+2726*x1^2*x3*x4+2092*x1*x2^2*x3-9310*x1*x2*x3^2-8820*x1*x2*x3*x4-56*x1*x3*x4^2+8465*x2^4-1104*x2^3*x3-13506*x2^3*x4-13091*x2^2*x3^2-5920*x2^2*x3*x4+8445*x2^2*x4^2-214*x2*x3^3+10066*x2*x3^2*x4+5476*x2*x3*x4^2-3080*x2*x4^3+7585*x3^4+9934*x3^3*x4+3578*x3^2*x4^2+784*x4^4-13800*x1*x2^2+1090*x1*x2*x3+11100*x1*x2*x4+10800*x1*x3^2+5550*x1*x3*x4+190*x2^3+10450*x2^2*x4-5320*x2*x4^2+6089*x1^2-1520*x1*x2+154*x1*x3+9179*x2^2-176*x2*x3+8470*x2*x4+784*x3^2+752*x3*x4-4312*x4^2+14630*x2+5993, -5510*x1^3+18050*x1^2*x2-638*x1^2*x3+4184*x1*x2*x3-9310*x1*x3^2-8820*x1*x3*x4+33860*x2^3-3312*x2^2*x3-40518*x2^2*x4-26182*x2*x3^2-11840*x2*x3*x4+16890*x2*x4^2-214*x3^3+10066*x3^2*x4+5476*x3*x4^2-3080*x4^3-27600*x1*x2+1090*x1*x3+11100*x1*x4+570*x2^2+20900*x2*x4-5320*x4^2-1520*x1+18358*x2-176*x3+8470*x4+14630, -638*x1^2*x2+5686*x1^2*x3+2726*x1^2*x4+2092*x1*x2^2-18620*x1*x2*x3-8820*x1*x2*x4-56*x1*x4^2-1104*x2^3-26182*x2^2*x3-5920*x2^2*x4-642*x2*x3^2+20132*x2*x3*x4+5476*x2*x4^2+30340*x3^3+29802*x3^2*x4+7156*x3*x4^2+1090*x1*x2+21600*x1*x3+5550*x1*x4+154*x1-176*x2+1568*x3+752*x4, 2726*x1^2*x3-8820*x1*x2*x3-112*x1*x3*x4-13506*x2^3-5920*x2^2*x3+16890*x2^2*x4+10066*x2*x3^2+10952*x2*x3*x4-9240*x2*x4^2+9934*x3^3+7156*x3^2*x4+3136*x4^3+11100*x1*x2+5550*x1*x3+10450*x2^2-10640*x2*x4+8470*x2+752*x3-8624*x4];
println(@elapsed SignatureGB.f5([841*x1^4-5510*x1^3*x2+9025*x1^2*x2^2-638*x1^2*x2*x3+2843*x1^2*x3^2+2726*x1^2*x3*x4+2092*x1*x2^2*x3-9310*x1*x2*x3^2-8820*x1*x2*x3*x4-56*x1*x3*x4^2+8465*x2^4-1104*x2^3*x3-13506*x2^3*x4-13091*x2^2*x3^2-5920*x2^2*x3*x4+8445*x2^2*x4^2-214*x2*x3^3+10066*x2*x3^2*x4+5476*x2*x3*x4^2-3080*x2*x4^3+7585*x3^4+9934*x3^3*x4+3578*x3^2*x4^2+784*x4^4-13800*x1*x2^2+1090*x1*x2*x3+11100*x1*x2*x4+10800*x1*x3^2+5550*x1*x3*x4+190*x2^3+10450*x2^2*x4-5320*x2*x4^2+6089*x1^2-1520*x1*x2+154*x1*x3+9179*x2^2-176*x2*x3+8470*x2*x4+784*x3^2+752*x3*x4-4312*x4^2+14630*x2+5993, -5510*x1^3+18050*x1^2*x2-638*x1^2*x3+4184*x1*x2*x3-9310*x1*x3^2-8820*x1*x3*x4+33860*x2^3-3312*x2^2*x3-40518*x2^2*x4-26182*x2*x3^2-11840*x2*x3*x4+16890*x2*x4^2-214*x3^3+10066*x3^2*x4+5476*x3*x4^2-3080*x4^3-27600*x1*x2+1090*x1*x3+11100*x1*x4+570*x2^2+20900*x2*x4-5320*x4^2-1520*x1+18358*x2-176*x3+8470*x4+14630, -638*x1^2*x2+5686*x1^2*x3+2726*x1^2*x4+2092*x1*x2^2-18620*x1*x2*x3-8820*x1*x2*x4-56*x1*x4^2-1104*x2^3-26182*x2^2*x3-5920*x2^2*x4-642*x2*x3^2+20132*x2*x3*x4+5476*x2*x4^2+30340*x3^3+29802*x3^2*x4+7156*x3*x4^2+1090*x1*x2+21600*x1*x3+5550*x1*x4+154*x1-176*x2+1568*x3+752*x4, 2726*x1^2*x3-8820*x1*x2*x3-112*x1*x3*x4-13506*x2^3-5920*x2^2*x3+16890*x2^2*x4+10066*x2*x3^2+10952*x2*x3*x4-9240*x2*x4^2+9934*x3^3+7156*x3^2*x4+3136*x4^3+11100*x1*x2+5550*x1*x3+10450*x2^2-10640*x2*x4+8470*x2+752*x3-8624*x4], verbose=true));exit()
