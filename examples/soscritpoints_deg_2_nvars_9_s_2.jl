using SignatureGB
using Singular
P, (x1, x2, x3, x4, x5, x6, x7, x8, x9)  = Singular.PolynomialRing(Fp(65521), ["x1", "x2", "x3", "x4", "x5", "x6", "x7", "x8", "x9"]);
gb = SignatureGB.f5([x1, x2, x3, x4, x5, x6, x7, x8, x9]);F = [3969*x1^2*x7^2-630*x1^2*x7*x9+25*x1^2*x9^2-4158*x1*x3^2*x7+330*x1*x3^2*x9+7308*x1*x3*x5*x7-580*x1*x3*x5*x9+4662*x1*x7*x9^2-370*x1*x9^3+64*x2^2*x8^2-848*x2*x3*x5*x8-784*x2*x8*x9^2+1089*x3^4-3828*x3^3*x5+6173*x3^2*x5^2-2442*x3^2*x9^2+9486*x3*x5*x9^2+3770*x9^4-128*x2^2*x8+848*x2*x3*x5-128*x2*x5*x8+784*x2*x9^2+848*x3*x5^2+784*x5*x9^2-10584*x1*x7+840*x1*x9+64*x2^2+128*x2*x5+1424*x2*x8+5544*x3^2-19178*x3*x5+64*x5^2-14938*x9^2-1424*x2-1424*x5+14977, 128*x2*x8^2-848*x3*x5*x8-784*x8*x9^2-256*x2*x8+848*x3*x5-128*x5*x8+784*x9^2+128*x2+128*x5+1424*x8-1424, -8316*x1*x3*x7+660*x1*x3*x9+7308*x1*x5*x7-580*x1*x5*x9-848*x2*x5*x8+4356*x3^3-11484*x3^2*x5+12346*x3*x5^2-4884*x3*x9^2+9486*x5*x9^2+848*x2*x5+848*x5^2+11088*x3-19178*x5, 0, 7308*x1*x3*x7-580*x1*x3*x9-848*x2*x3*x8-3828*x3^3+12346*x3^2*x5+9486*x3*x9^2+848*x2*x3-128*x2*x8+1696*x3*x5+784*x9^2+128*x2-19178*x3+128*x5-1424, 0, 7938*x1^2*x7-630*x1^2*x9-4158*x1*x3^2+7308*x1*x3*x5+4662*x1*x9^2-10584*x1, 128*x2^2*x8-848*x2*x3*x5-784*x2*x9^2-128*x2^2-128*x2*x5+1424*x2, -630*x1^2*x7+50*x1^2*x9+330*x1*x3^2-580*x1*x3*x5+9324*x1*x7*x9-1110*x1*x9^2-1568*x2*x8*x9-4884*x3^2*x9+18972*x3*x5*x9+15080*x9^3+1568*x2*x9+1568*x5*x9+840*x1-29876*x9];
println(@elapsed SignatureGB.f5([3969*x1^2*x7^2-630*x1^2*x7*x9+25*x1^2*x9^2-4158*x1*x3^2*x7+330*x1*x3^2*x9+7308*x1*x3*x5*x7-580*x1*x3*x5*x9+4662*x1*x7*x9^2-370*x1*x9^3+64*x2^2*x8^2-848*x2*x3*x5*x8-784*x2*x8*x9^2+1089*x3^4-3828*x3^3*x5+6173*x3^2*x5^2-2442*x3^2*x9^2+9486*x3*x5*x9^2+3770*x9^4-128*x2^2*x8+848*x2*x3*x5-128*x2*x5*x8+784*x2*x9^2+848*x3*x5^2+784*x5*x9^2-10584*x1*x7+840*x1*x9+64*x2^2+128*x2*x5+1424*x2*x8+5544*x3^2-19178*x3*x5+64*x5^2-14938*x9^2-1424*x2-1424*x5+14977, 128*x2*x8^2-848*x3*x5*x8-784*x8*x9^2-256*x2*x8+848*x3*x5-128*x5*x8+784*x9^2+128*x2+128*x5+1424*x8-1424, -8316*x1*x3*x7+660*x1*x3*x9+7308*x1*x5*x7-580*x1*x5*x9-848*x2*x5*x8+4356*x3^3-11484*x3^2*x5+12346*x3*x5^2-4884*x3*x9^2+9486*x5*x9^2+848*x2*x5+848*x5^2+11088*x3-19178*x5, 0, 7308*x1*x3*x7-580*x1*x3*x9-848*x2*x3*x8-3828*x3^3+12346*x3^2*x5+9486*x3*x9^2+848*x2*x3-128*x2*x8+1696*x3*x5+784*x9^2+128*x2-19178*x3+128*x5-1424, 0, 7938*x1^2*x7-630*x1^2*x9-4158*x1*x3^2+7308*x1*x3*x5+4662*x1*x9^2-10584*x1, 128*x2^2*x8-848*x2*x3*x5-784*x2*x9^2-128*x2^2-128*x2*x5+1424*x2, -630*x1^2*x7+50*x1^2*x9+330*x1*x3^2-580*x1*x3*x5+9324*x1*x7*x9-1110*x1*x9^2-1568*x2*x8*x9-4884*x3^2*x9+18972*x3*x5*x9+15080*x9^3+1568*x2*x9+1568*x5*x9+840*x1-29876*x9], verbose=true));exit()
