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
include("./interreduction.jl")
include("./gen_example_file.jl")

function f5setup(I::Vector{P};
                 start_gen = 1,
                 mod_order=:POT,
                 mon_order=:GREVLEX,
                 index_type=UInt32,
                 mask_type=UInt32,
                 pos_type=UInt32,
                 max_remasks=3,
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
                 pos_type = pos_type, order = order,
                 max_remasks = max_remasks)
    ctx = dat.ctx
    G = new_basis(ctx, length(I))
    for i in 1:(start_gen - 1)
        lm = leadingmonomial(ctx, (pos_type(i), ctx.po.mo(R(1))))
        push!(G[pos_type(i)], (ctx.po.mo(R(1)), lm))
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
                 interreduction = true,
                 verbose = false) where {I, M, SΓ <: SigPolynomialΓ{I, M}}
    
    ctx = dat.ctx
    use_max_sig = (select == select_all_pos_and_degree! || select == select_one!)
    
    cnt = 1
    num_arit_operations = 0
    curr_pos = zero(pos_type(ctx))

    while !(isempty(pairs))
        #- INTERREDUCTION -#
        indx = pos(first(pairs)[1])
        if indx != curr_pos && mod_order(dat.ctx) == :POT
            if dat.remasks_left > 0
                remask!(dat.ctx.po.mo.table)
                dat.remasks_left -= 1
            end
            if interreduction && indx > 2
                G = interreduce(ctx, G, H)
            end
            if verbose
                println("-----------")
                interreduction && indx > 2 && println("INTERREDUCING")
                println("STARTING WITH INDEX $(indx)")
                println("-----------")
            end
            curr_pos = indx
        end
        
        
        #- PAIR SELECTION -#
        total_num_pairs = length(pairs)
        to_reduce, are_pairs, nselected, sig_degree = select(ctx, pairs)

        #- SYMBOLIC PP -#
        symbolic_pp_timed  = @timed symbolic_pp!(ctx, to_reduce, G, H,
                                                 use_max_sig = use_max_sig,
                                                 sig_degree = sig_degree,
                                                 max_sig_pos = curr_pos,
                                                 are_pairs = are_pairs,
                                                 enable_lower_pos_rewrite = !(interreduction))
        done = symbolic_pp_timed.value
        symbolic_pp_time = symbolic_pp_timed.time
        to_reduce = sort(collect(to_reduce), lt = (a, b) -> Base.Order.lt(mpairordering(ctx), a, b))
        mat = f5matrix(ctx, done, to_reduce, enable_lower_pos_rewrite = !(interreduction))
        mat_size = (length(mat.rows), length(mat.tbl))
        mat_dens = sum([length(rw) for rw in mat.rows]) / (mat_size[1] * mat_size[2])

        #- REDUCTION -#
        reduction_dat = @timed reduction!(mat)
        num_arit_operations += reduction_dat.value

        #- PAIR GENERATION -#
        pair_gen_time = @elapsed new_elems_f5!(ctx, mat, pairs, G, H,
                                               enable_lower_pos_rewrite = !(interreduction))

        if verbose
            zero_red_count = 0
            println("selected $(nselected) / $(total_num_pairs) pairs, sig-degree of sel. pairs: $(sig_degree)")
            println("symbolic pp took $(symbolic_pp_time) seconds.")
            println("Matrix $(cnt) : $(reduction_dat.time) secs reduction / size = $(mat_size) / density = $(mat_dens)")
            for (sig, rw) in zip(mat.sigs, mat.rows)
                if isempty(rw)
                    zero_red_count += 1
                end
            end
            if !(iszero(zero_red_count))
                println("$(zero_red_count) zero reductions at sig-degree $(degree(ctx, last(mat.sigs))) / position $(pos(last(mat.sigs)))")
            end
            println("Pair generation took $(pair_gen_time) seconds.")
        end
        
        cnt += 1
    end

    if verbose
        println("-----")
        println("total number of arithmetic operations: $(num_arit_operations)")
    end
    G
end

function f5(I::Vector{P};
            start_gen = 1,
            mod_order=:POT,
            mon_order=:GREVLEX,
            index_type=UInt32,
            mask_type=UInt32,
            pos_type=UInt32,
            select = select_all_pos_and_degree!,
            verbose = false,
            interreduction = true,
            max_remasks = 3,
            kwargs...) where {P <: AA.MPolyElem}

    R = parent(first(I))
    dat, G, H, pairs = f5setup(I, start_gen = start_gen, mod_order = mod_order,
                               mon_order = mon_order, index_type = index_type,
                               mask_type = mask_type, pos_type = pos_type,
                               max_remasks = max_remasks, kwargs...)
    G = f5core!(dat, G, H, pairs, select = select, interreduction = interreduction, verbose = verbose)
    if interreduction
         G = interreduce(dat.ctx, G, H)
    end
    [R(dat.ctx, (i, g[1])) for i in keys(G) for g in G[i]]
end

end
