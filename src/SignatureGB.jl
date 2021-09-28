module SignatureGB

include("./useful.jl")
include("./sliceddict.jl")
include("./context.jl")
include("./termorder.jl")
include("./polynomials.jl")
include("./coefficients.jl")
include("./monomialtable.jl")
include("./sigtable.jl")
include("./f5data.jl")
include("./kd_tree.jl")
include("./pairs.jl")
include("./symbolicpp.jl")
include("./reduction.jl")

function f5setup(I::Vector{P};
                 start_gen = 1,
                 mod_order=:POT,
                 mon_order=:GREVLEX,
                 index_type=UInt32,
                 mask_type=UInt32,
                 pos_type=UInt32,
                 kwargs...) where {P <: AA.MPolyElem}

    R = parent(first(I))
    if mon_order == :GREVLEX
        order = Grevlex(AA.ngens(R))
    else
        error("only grevlex order currently supported")
    end
    dat = f5data(I, mod_order = mod_order, trace_sig_tails = false,
                 index_type = index_type, mask_type = mask_type,
                 pos_type = pos_type, order = order)
    ctx = dat.ctx
    G = SlicedInd([ctx(i, R(1)) for i in 1:start_gen - 1])
    H = SlicedInd(eltype(ctx)[])
    pairs = pairset(ctx)
    [pair!(ctx, pairs, ctx(i, R(1))) for i in start_gen:length(I)]
    dat, G, H, pairs
end

function f5core!(dat::F5Data{I, SΓ},
                 G::Basis{I, M},
                 H::Basis{I, M},
                 pairs::PairSet{I, M, SΓ},
                 select = select_one!) where {I, M, SΓ <: SigPolynomialΓ{I, M}}

    ctx = dat.ctx
    while !(isempty(pairs))
        to_reduce = select(ctx, pairs)
        pr = first(to_reduce)
        done = symbolic_pp!(ctx, to_reduce, G, H)
        mat = f5matrix(ctx, done, to_reduce)
        reduction!(mat)
        new_elems_f5!(ctx, mat, pairs, G, H)
    end
end


end
