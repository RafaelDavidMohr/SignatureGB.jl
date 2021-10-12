using SignatureGB
using Singular
P, (x1, x2, x3, x4)  = Singular.PolynomialRing(Fp(65521), ["x1", "x2", "x3", "x4"]);
gb = SignatureGB.f5([x1, x2, x3, x4]);F = [2297232*x1^4+10816588*x1^3*x2-19696652*x1^3*x3+12014836*x1^3*x4+19038581*x1^2*x2^2+25140479*x1^2*x2*x3-124056256*x1^2*x2*x4-19352961*x1^2*x3^2+30086207*x1^2*x3*x4-15861565*x1^2*x4^2-64545276*x1*x2^3-3395230*x1*x2^2*x3+125153935*x1*x2^2*x4-10319588*x1*x2*x3^2+5839912*x1*x2*x3*x4+112915639*x1*x2*x4^2+12114032*x1*x3^3+32314614*x1*x3^2*x4-5646418*x1*x3*x4^2-3823868*x1*x4^3+40572828*x2^4-42051502*x2^3*x3-17361686*x2^3*x4+66618627*x2^2*x3^2-61020343*x2^2*x3*x4-66491064*x2^2*x4^2+16298428*x2*x3^3+46623254*x2*x3^2*x4-26720875*x2*x3*x4^2-16047619*x2*x4^3+15073900*x3^4+9644976*x3^3*x4-9790086*x3^2*x4^2-9372130*x3*x4^3+4661500*x4^4-39813328*x1^3-9400295*x1^2*x2-1289811*x1^2*x3+64756487*x1^2*x4-41226416*x1*x2^2+22255617*x1*x2*x3+115474646*x1*x2*x4+54583668*x1*x3^2+150465505*x1*x3*x4-19224417*x1*x4^2+52554279*x2^3-1318549*x2^2*x3-91874169*x2^2*x4+119183502*x2*x3^2-131012023*x2*x3*x4-88321124*x2*x4^2+41605616*x3^3+58052114*x3^2*x4-70772721*x3*x4^2+3123219*x4^3+99968607*x1^2-17533608*x1*x2+133696391*x1*x3-71771275*x1*x4+20484256*x2^2+10206682*x2*x3-58141098*x2*x4+72704712*x3^2-111938286*x3*x4-5946966*x4^2-46338000*x1+12230767*x2-23665371*x3+7665457*x4+9313394, 10816588*x1^3+38077162*x1^2*x2+25140479*x1^2*x3-124056256*x1^2*x4-193635828*x1*x2^2-6790460*x1*x2*x3+250307870*x1*x2*x4-10319588*x1*x3^2+5839912*x1*x3*x4+112915639*x1*x4^2+162291312*x2^3-126154506*x2^2*x3-52085058*x2^2*x4+133237254*x2*x3^2-122040686*x2*x3*x4-132982128*x2*x4^2+16298428*x3^3+46623254*x3^2*x4-26720875*x3*x4^2-16047619*x4^3-9400295*x1^2-82452832*x1*x2+22255617*x1*x3+115474646*x1*x4+157662837*x2^2-2637098*x2*x3-183748338*x2*x4+119183502*x3^2-131012023*x3*x4-88321124*x4^2-17533608*x1+40968512*x2+10206682*x3-58141098*x4+12230767, -19696652*x1^3+25140479*x1^2*x2-38705922*x1^2*x3+30086207*x1^2*x4-3395230*x1*x2^2-20639176*x1*x2*x3+5839912*x1*x2*x4+36342096*x1*x3^2+64629228*x1*x3*x4-5646418*x1*x4^2-42051502*x2^3+133237254*x2^2*x3-61020343*x2^2*x4+48895284*x2*x3^2+93246508*x2*x3*x4-26720875*x2*x4^2+60295600*x3^3+28934928*x3^2*x4-19580172*x3*x4^2-9372130*x4^3-1289811*x1^2+22255617*x1*x2+109167336*x1*x3+150465505*x1*x4-1318549*x2^2+238367004*x2*x3-131012023*x2*x4+124816848*x3^2+116104228*x3*x4-70772721*x4^2+133696391*x1+10206682*x2+145409424*x3-111938286*x4-23665371, 12014836*x1^3-124056256*x1^2*x2+30086207*x1^2*x3-31723130*x1^2*x4+125153935*x1*x2^2+5839912*x1*x2*x3+225831278*x1*x2*x4+32314614*x1*x3^2-11292836*x1*x3*x4-11471604*x1*x4^2-17361686*x2^3-61020343*x2^2*x3-132982128*x2^2*x4+46623254*x2*x3^2-53441750*x2*x3*x4-48142857*x2*x4^2+9644976*x3^3-19580172*x3^2*x4-28116390*x3*x4^2+18646000*x4^3+64756487*x1^2+115474646*x1*x2+150465505*x1*x3-38448834*x1*x4-91874169*x2^2-131012023*x2*x3-176642248*x2*x4+58052114*x3^2-141545442*x3*x4+9369657*x4^2-71771275*x1-58141098*x2-111938286*x3-11893932*x4+7665457];
@time gb = SignatureGB.f5([2297232*x1^4+10816588*x1^3*x2-19696652*x1^3*x3+12014836*x1^3*x4+19038581*x1^2*x2^2+25140479*x1^2*x2*x3-124056256*x1^2*x2*x4-19352961*x1^2*x3^2+30086207*x1^2*x3*x4-15861565*x1^2*x4^2-64545276*x1*x2^3-3395230*x1*x2^2*x3+125153935*x1*x2^2*x4-10319588*x1*x2*x3^2+5839912*x1*x2*x3*x4+112915639*x1*x2*x4^2+12114032*x1*x3^3+32314614*x1*x3^2*x4-5646418*x1*x3*x4^2-3823868*x1*x4^3+40572828*x2^4-42051502*x2^3*x3-17361686*x2^3*x4+66618627*x2^2*x3^2-61020343*x2^2*x3*x4-66491064*x2^2*x4^2+16298428*x2*x3^3+46623254*x2*x3^2*x4-26720875*x2*x3*x4^2-16047619*x2*x4^3+15073900*x3^4+9644976*x3^3*x4-9790086*x3^2*x4^2-9372130*x3*x4^3+4661500*x4^4-39813328*x1^3-9400295*x1^2*x2-1289811*x1^2*x3+64756487*x1^2*x4-41226416*x1*x2^2+22255617*x1*x2*x3+115474646*x1*x2*x4+54583668*x1*x3^2+150465505*x1*x3*x4-19224417*x1*x4^2+52554279*x2^3-1318549*x2^2*x3-91874169*x2^2*x4+119183502*x2*x3^2-131012023*x2*x3*x4-88321124*x2*x4^2+41605616*x3^3+58052114*x3^2*x4-70772721*x3*x4^2+3123219*x4^3+99968607*x1^2-17533608*x1*x2+133696391*x1*x3-71771275*x1*x4+20484256*x2^2+10206682*x2*x3-58141098*x2*x4+72704712*x3^2-111938286*x3*x4-5946966*x4^2-46338000*x1+12230767*x2-23665371*x3+7665457*x4+9313394, 10816588*x1^3+38077162*x1^2*x2+25140479*x1^2*x3-124056256*x1^2*x4-193635828*x1*x2^2-6790460*x1*x2*x3+250307870*x1*x2*x4-10319588*x1*x3^2+5839912*x1*x3*x4+112915639*x1*x4^2+162291312*x2^3-126154506*x2^2*x3-52085058*x2^2*x4+133237254*x2*x3^2-122040686*x2*x3*x4-132982128*x2*x4^2+16298428*x3^3+46623254*x3^2*x4-26720875*x3*x4^2-16047619*x4^3-9400295*x1^2-82452832*x1*x2+22255617*x1*x3+115474646*x1*x4+157662837*x2^2-2637098*x2*x3-183748338*x2*x4+119183502*x3^2-131012023*x3*x4-88321124*x4^2-17533608*x1+40968512*x2+10206682*x3-58141098*x4+12230767, -19696652*x1^3+25140479*x1^2*x2-38705922*x1^2*x3+30086207*x1^2*x4-3395230*x1*x2^2-20639176*x1*x2*x3+5839912*x1*x2*x4+36342096*x1*x3^2+64629228*x1*x3*x4-5646418*x1*x4^2-42051502*x2^3+133237254*x2^2*x3-61020343*x2^2*x4+48895284*x2*x3^2+93246508*x2*x3*x4-26720875*x2*x4^2+60295600*x3^3+28934928*x3^2*x4-19580172*x3*x4^2-9372130*x4^3-1289811*x1^2+22255617*x1*x2+109167336*x1*x3+150465505*x1*x4-1318549*x2^2+238367004*x2*x3-131012023*x2*x4+124816848*x3^2+116104228*x3*x4-70772721*x4^2+133696391*x1+10206682*x2+145409424*x3-111938286*x4-23665371, 12014836*x1^3-124056256*x1^2*x2+30086207*x1^2*x3-31723130*x1^2*x4+125153935*x1*x2^2+5839912*x1*x2*x3+225831278*x1*x2*x4+32314614*x1*x3^2-11292836*x1*x3*x4-11471604*x1*x4^2-17361686*x2^3-61020343*x2^2*x3-132982128*x2^2*x4+46623254*x2*x3^2-53441750*x2*x3*x4-48142857*x2*x4^2+9644976*x3^3-19580172*x3^2*x4-28116390*x3*x4^2+18646000*x4^3+64756487*x1^2+115474646*x1*x2+150465505*x1*x3-38448834*x1*x4-91874169*x2^2-131012023*x2*x3-176642248*x2*x4+58052114*x3^2-141545442*x3*x4+9369657*x4^2-71771275*x1-58141098*x2-111938286*x3-11893932*x4+7665457], verbose=true);[leading_monomial(g) for g in gb];exit()