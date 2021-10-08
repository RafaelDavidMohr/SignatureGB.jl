using Singular

function cyclic(vars)
    n = length(vars)
    pols = [sum(prod(vars[j%n+1] for j in k:k+i) for k in 1:n) for i in 0:n-2]
    push!(pols, prod(vars[i] for i in 1:n)-1)
    return pols
end

function gen_example_file(I::Vector{MP},
                          filename::String) where {MP <: AbstractAlgebra.MPolyElem}
    f = open(string(filename, ".jl"), write = true, create = true)
    println(f, "using Singular")
    println(f, "using SignatureGB")
    R = parent(first(I))
    vars = ["x$(i)" for i in 1:Singular.nvars(R)]
    println(f, "R, ($(vars...)) = Singular.PolynomialRing(Fp($(Singular.characteristic(R))), $(vars))") 
    println(f, "I = $(I)")
    println(f, "comp_ideal = gens(R)")
    println(f, "SignatureGB.f5(comp_ideal)")
    println(f, "SignatureGB.f5(I, verbose = true)")
    close(f)
end