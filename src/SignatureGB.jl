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
include("./siggbtests.jl")

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
        order = Grevlex(Singular.nvars(R))
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
        new_basis_elem!(G[pos_type(i)], ctx.po.mo(R(1)))
    end
    H = new_syz(ctx, length(I))
    pairs = pairset(ctx)
    [pair!(ctx, pairs, ctx(i, R(1))) for i in start_gen:length(I)]
    dat, G, H, pairs
end

function f5core!(dat::F5Data{I, SΓ},
                 G::Basis{I, M},
                 H::Syz{I, M},
                 pairs::PairSet{I, M, SΓ};
                 select = select_all_pos_and_degree!,
                 verbose = false) where {I, M, SΓ <: SigPolynomialΓ{I, M}}
    
    ctx = dat.ctx
    cnt = 1
    num_arit_operations = 0
    curr_pos = zero(pos_type(ctx))
    deg_pair = p -> degree(ctx.po.mo, p[1]) + degree(ctx.po.mo, p[2][2])
    while !(isempty(pairs))
        #- PAIR SELECTION -#
        total_num_pairs = length(pairs)
        to_reduce, are_pairs, nselected = select(ctx, pairs)
        sig_degree = deg_pair(first(to_reduce))
        if verbose && pos(first(to_reduce)) != curr_pos
            println("-----------")
            println("STARTING WITH INDEX $(pos(first(to_reduce)))")
            println("-----------")
            curr_pos = pos(first(to_reduce))
        end

        #- SYMBOLIC PP -#
        symbolic_pp_timed  = @timed symbolic_pp!(ctx, to_reduce, G, H, are_pairs = are_pairs)
        done = symbolic_pp_timed.value
        symbolic_pp_time = symbolic_pp_timed.time
        mat = f5matrix(ctx, done, to_reduce)
        mat_size = (length(mat.rows), length(mat.tbl))
        mat_dens = sum([length(rw) for rw in mat.rows]) / (mat_size[1] * mat_size[2])

        #- REDUCTION -#
        reduction_dat = @timed reduction!(mat)
        num_arit_operations += reduction_dat.value

        #- PAIR GENERATION -#
        pair_gen_time = @elapsed new_elems_f5!(ctx, mat, pairs, G, H)

        if verbose
            println("selected $(nselected) / $(total_num_pairs) pairs, sig-degree of sel. pairs: $(sig_degree)")
            println("symbolic pp took $(symbolic_pp_time) seconds.")
            println("Matrix $(cnt) : $(reduction_dat.time) secs reduction / size = $(mat_size) / density = $(mat_dens)")
            for (sig, rw) in zip(mat.sigs, mat.rows)
                if isempty(rw)
                    println("zero reduction at sig-degree $(deg_pair(sig)) / position $(pos(sig))")
                end
            end
            println("Pair generation took $(pair_gen_time) seconds.")
        end
        
        cnt += cnt + 1
    end

    if verbose
        println("-----")
        println("total number of arithmetic operations: $(num_arit_operations)")
    end
end

function f5(I::Vector{P},
            start_gen = 1,
            mod_order=:POT,
            mon_order=:GREVLEX,
            index_type=UInt32,
            mask_type=UInt32,
            pos_type=UInt32,
            select = select_all_pos!,
            kwargs...) where {P <: AA.MPolyElem}

    R = parent(first(I))
    dat, G, H, pairs = f5setup(I, start_gen = start_gen, mod_order = mod_order,
                               mon_order = mon_order, index_type = index_type,
                               mask_type = mask_type, pos_type = pos_type,
                               kwargs...)
    f5core!(dat, G, H, pairs, select = select)
    [R(dat.ctx, (i, g[1])) for i in keys(G) for g in G[i]]
end

end
