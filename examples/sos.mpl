#You can also play with deg
deg:=2:
for n from 4 to 10 do 
  for s from 2 to n-1 do 
    vars:=[seq(cat(x,i),i=1..n)]:
    f:=expand(add(randpoly(vars,degree=deg)^2,i=1..s)):

    #To decompose
    F:=[f, seq(diff(f,v), v in vars[2..n])]:

#  rr:=rand(1..512):
#  l:=add(rr()*v, v in vars):

#  J:=linalg:-jacobian([f,l], vars):
#  J:=convert(J, Matrix):
#  with(LinearAlgebra):
#  lcols:=combinat:-choose(n, 2):

#  #To decompose
#  F1:=[f, seq(Determinant(SubMatrix(J, [1,2], cols)), cols in lcols)]:

   str:=cat("./soscritpoints_deg_", deg, "_nvars_", n, "_s_",s,".jl");
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
   fprintf(fd, "gb = SignatureGB.f5(%a, verbose=true);", F);
   fprintf(fd, "[leading_monomial(g) for g in gb];");
   fprintf(fd, "exit()\n");
   fclose(fd):
  od:
od:
