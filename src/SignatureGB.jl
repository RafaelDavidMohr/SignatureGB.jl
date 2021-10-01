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

mutable struct Timings
    reduction::Float64
    rewrite::Float64
    new_rewriter::Float64
end

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
    if mod_order != :POT
        error("only position over term order currently supported")
    end
    dat = f5data(I, mod_order = mod_order, trace_sig_tails = false,
                 index_type = index_type, mask_type = mask_type,
                 pos_type = pos_type, order = order)
    ctx = dat.ctx
    G = new_basis(ctx, length(I))
    for i in 1:(start_gen - 1)
        push!(G[pos_type(i)], ctx.po.mo(R(1)))
    end
    H = new_basis(ctx, length(I))
    pairs = pairset(ctx)
    [pair!(ctx, pairs, ctx(i, R(1))) for i in start_gen:length(I)]
    dat, G, H, pairs
end

function f5core!(dat::F5Data{I, SΓ},
                 G::Basis{I, M},
                 H::Basis{I, M},
                 pairs::PairSet{I, M, SΓ},
                 select = select_one!) where {I, M, SΓ <: SigPolynomialΓ{I, M}}

    times = Timings(0.0, 0.0, 0.0)
    
    ctx = dat.ctx
    while !(isempty(pairs))
        to_reduce, are_pairs = select_one!(ctx, pairs)
        pr = last(to_reduce)
        done, rewrite_checks_time =  symbolic_pp!(ctx, to_reduce, G, H, are_pairs = are_pairs)
        times.rewrite += rewrite_checks_time
        mat = f5matrix(ctx, done, to_reduce)
        times.reduction += @elapsed reduction!(mat)
        @debug "is in row echelon:" check_row_echelon(mat)
        @debug "row signatures:" [pretty_print(ctx, sig) for sig in mat.sigs if pos(sig) == pos(last(mat.sigs))]
        new_rewriter_time, rewrite_checks_time = new_elems_f5!(ctx, mat, pairs, G, H)
        times.rewrite += rewrite_checks_time
        times.new_rewriter += new_rewriter_time
        @debug "current basis in relevant position:" [(Int(g[1]), pretty_print(ctx.po.mo, g[2])) for g in G if g[1] == pos(last(mat.sigs))]
    end

    times
end


end
