#Play with n, deg and s to have larger examples
deg:=2:
for n from 4 to 10 do 

    vars:=[seq(cat(x,i),i=1..n+1)]:
    f1:=expand(randpoly(vars,degree=deg, dense));
    f2:=expand(randpoly(vars,degree=deg, dense)):
    f:=resultant(f1, f2, vars[-1]);

    #To decompose
    F:=[f, seq(diff(f,v), v in vars[2..n])]:
    print(nops(F), nops(vars[1..n]), degree(f));
#    FGb:-fgb_matrixn_radical([l*diff(f, vars[1])-1, op(F)], 0, [l, op(vars[1..n])], 0, {"verb"=3});

   str:=cat("./singhypcritpoints_deg_", deg, "_nvars_", n, ".jl");
   fd:=fopen(str, WRITE):
   fprintf(fd, "using SignatureGB\n");
   fprintf(fd, "using Singular\n");

   fprintf(fd, "P, (%a, ", vars[1]);
   for j from 2 to n-1 do
   fprintf(fd, "%a, ", vars[j]);
   od:
   fprintf(fd, "%a)  = Singular.PolynomialRing(Fp(65521), [", vars[n]);
   for j from 1 to n-1 do
   fprintf(fd, "\"%a\", ", vars[j]);
   od:
   fprintf(fd, "\"%a\"]);\n", vars[n]);
   fprintf(fd, "gb = SignatureGB.f5(%a);", vars[1..n]);

   fprintf(fd, "F = %a;\n", F);
   fprintf(fd, "@time gb = SignatureGB.f5(%a, verbose=true);", F);
   fprintf(fd, "[leading_monomial(g) for g in gb];");
   fprintf(fd, "exit()\n");
   fclose(fd):

od:
