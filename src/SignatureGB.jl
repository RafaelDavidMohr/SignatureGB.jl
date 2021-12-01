module SignatureGB

const Info = Dict{String, Int}
new_info() = Dict([("arit_ops_groebner", 0),
                   ("arit_ops_module", 0),
                   ("arit_ops_interred", 0),
                   ("interred_mat_size_rows", 0),
                   ("interred_mat_size_cols", 0),
                   ("num_zero_red", 0)])

include("./useful.jl")
include("./context.jl")
include("./termorder.jl")
include("./polynomials.jl")
include("./coefficients.jl")
include("./monomialtable.jl")
include("./sigtable.jl")
include("./f5data.jl")
include("./pairs.jl")
include("./symbolicpp.jl")
include("./reduction.jl")
include("./interreduction.jl")
include("./gen_example_file.jl")

export f5, decompose

# converting a vector of singular polynomials into our own data structures
function f5setup(I::Vector{P};
                 mod_order=:POT,
                 mon_order=:GREVLEX,
                 index_type=UInt32,
                 mask_type=UInt32,
                 pos_type=UInt32,
                 trace_sig_tail_tags = Symbol[],
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
    dat = f5data(I, mod_order = mod_order, trace_sig_tail_tags = trace_sig_tail_tags,
                 index_type = index_type, mask_type = mask_type,
                 pos_type = pos_type, order = order,
                 max_remasks = max_remasks)
end

# build initial pairset, basis and syzygies
function pairs_and_basis(dat::F5Data,
                         basis_length;
                         start_gen = 1)

    R = dat.R
    ctx = dat.ctx
    G = new_basis(ctx, basis_length)
    pos_t = pos_type(ctx)
    for i in 1:(start_gen - 1)
        lm = leadingmonomial(ctx, (pos_t(i), ctx.po.mo(R(1))))
        push!(G[pos_t(i)], (ctx.po.mo(R(1)), lm))
    end
    H = new_syz(ctx, basis_length)
    pairs = pairset(ctx)
    [pair!(ctx, pairs, ctx(i, R(1))) for i in start_gen:basis_length]
    G, H, pairs
end

function f5core!(dat::F5Data{I, SΓ},
                 G::Basis{I, M},
                 H::Syz{I, M},
                 pairs::PairSet{I, M, SΓ};
                 select = :deg_and_pos,
                 new_elems = new_elems_f5!,
                 interreduction = true,
                 select_both = true,
                 verbose = false,
                 saturate = false) where {I, M, SΓ <: SigPolynomialΓ{I, M}}
    
    ctx = dat.ctx
    R = dat.R
    use_max_sig = (select == :deg_and_pos || select == :pos)
    orig_length = length(ctx.ord_indices)

    info_hashmap = Dict([(i, new_info()) for i in keys(ctx.ord_indices)])
    mat_cnt = 0
    global_zero_red_count = 0
    num_arit_operations_groebner = 0
    num_arit_operations_module_overhead = 0
    num_arit_operations_interreduction = 0
    verbose_groebner = verbose && !(saturate)
    verbose_saturate = verbose && saturate
    
    curr_pos = zero(pos_type(ctx))
    curr_pos_key = zero(pos_type(ctx))
    curr_tag = :f

    non_zero_cond = eltype(ctx.po)[]

    while !(isempty(pairs))
        #- INTERREDUCTION -#
        indx = pos(ctx, first(pairs)[1])
        if indx != curr_pos && mod_order(dat.ctx) == :POT

            # here we do several steps when the index jumps:
            # possibly remasking
            if dat.remasks_left > 0
                remask!(dat.ctx.po.mo.table)
                dat.remasks_left -= 1
            end

            # if we are in a decomposition computation we add non-zero conditions
            if curr_tag == :g_prime && !(saturate)
                non_zero_cond_local_sigs = [(curr_pos_key, m) for m in H[curr_pos_key]]
                non_zero_cond_local = eltype(ctx.po)[]
                for sig in non_zero_cond_local_sigs
                    try
                        push!(non_zero_cond_local, project(ctx, sig))
                    catch
                        continue
                    end
                end
                if !(isempty(non_zero_cond_local))
                    push!(non_zero_cond, random_lin_comb(ctx.po, non_zero_cond_local))
                end
            end

            # interreducing
            if interreduction && indx > 2
                verbose_groebner && println("INTERREDUCING")
                G, arit_ops = interreduce(ctx, G, H, verbose = verbose_groebner)
                info_hashmap[curr_pos_key]["num_arit_ops_interred"] = arit_ops
            end
        end
        # update current index, current tag and current index key
        curr_pos = indx
        curr_tag = gettag(ctx, first(pairs)[1])
        curr_pos_key = first(pairs)[1][2][1]

        #- PAIR SELECTION -#
        total_num_pairs = length(pairs)
        to_reduce, are_pairs, nselected, sig_degree = select!(ctx, pairs, Val(select), select_both = select_both)

        #- SYMBOLIC PP -#
        symbolic_pp_timed  = @timed symbolic_pp!(ctx, to_reduce, G, H,
                                                 use_max_sig = use_max_sig,
                                                 sig_degree = sig_degree,
                                                 max_sig_pos = curr_pos,
                                                 are_pairs = are_pairs,
                                                 enable_lower_pos_rewrite = !(interreduction))
        done = symbolic_pp_timed.value
        symbolic_pp_time = symbolic_pp_timed.time
        mat = f5matrix(ctx, done, collect(to_reduce), curr_pos, curr_pos_key, curr_tag,
                       trace_sig_tail_tags = dat.trace_sig_tail_tags,
                       enable_lower_pos_rewrite = !(interreduction))
        mat_size = (length(rows(mat)), length(mat.tbl))
        mat_dens = sum([length(rw) for rw in rows(mat)]) / (mat_size[1] * mat_size[2])

        #- REDUCTION -#
        reduction_dat = @timed reduction!(mat)

        # storing computational information
        zero_red_count = length(filter(sig_rw -> isempty(sig_rw[2]), mat.sigs_rows))
        info_hashmap[curr_pos_key]["arit_ops_groebner"] += reduction_dat.value[1]
        info_hashmap[curr_pos_key]["arit_ops_module"] += reduction_dat.value[2]
        info_hashmap[curr_pos_key]["num_zero_red"] += zero_red_count

        #- PAIR GENERATION -#
        pair_gen_dat = @timed new_elems(ctx, mat, pairs, G, H, info_hashmap,
                                        enable_lower_pos_rewrite = !(interreduction))
        pairs = pair_gen_dat.value
        pair_gen_time = pair_gen_dat.time

        #- PRINTING INFORMATION -#
        if verbose_groebner
            mat_cnt += 1
            if verbose_groebner
                println("selected $(nselected) / $(total_num_pairs) pairs, sig-degree of sel. pairs: $(sig_degree)")
                println("symbolic pp took $(symbolic_pp_time) seconds.")
                println("Matrix $(mat_cnt) : $(reduction_dat.time) secs reduction / size = $(mat_size) / density = $(mat_dens)")
            end
            for (sig, rw) in mat.sigs_rows
                if isempty(rw)
                    if gettag(ctx, sig) == :f
                        global_zero_red_count +=1
                    end
                end
            end
            if !(iszero(zero_red_count))
                println("$(zero_red_count) zero reductions at sig-degree $(sig_degree) / position $(curr_pos)")
            end
            verbose_groebner && println("Pair generation took $(pair_gen_time) seconds.")
        end
    end

    verbose_groebner && println("-----")

    if saturate
        G[curr_pos_key] = Tuple{M, M}[]
    end
        
    if interreduction
        verbose_groebner && println("FINAL INTERREDUCTION STEP")
        G, arit_ops = interreduce(ctx, G, H, verbose = verbose_groebner)
        num_arit_operations_interreduction += arit_ops
        verbose_groebner && println("-----")
    end
    
    if verbose
        println("-----")
        num_arit_operations_groebner = 0
        num_arit_operations_module_overhead = 0
        num_arit_operations_interreduction = 0
        for (k, info) in info_hashmap
            arit_ops_groebner = info["arit_ops_groebner"]
            arit_ops_module = info["arit_ops_module"]
            arit_ops_interred = info["arit_ops_interred"]
            interred_mat_size_rows = info["interred_mat_size_rows"]
            interred_mat_size_cols = info["interred_mat_size_cols"]
            num_zero_red = info["num_zero_red"]
            num_arit_operations_groebner += arit_ops_groebner
            num_arit_operations_module_overhead += arit_ops_module
            num_arit_operations_interreduction += arit_ops_interred
            if k < orig_length
                println("INFO for index $(ctx.ord_indices[k][:position]), original index $(k), tagged $(ctx.ord_indices[k][:tag])")
            else
                println("INFO for index $(ctx.ord_indices[k][:position]), tagged $(ctx.ord_indices[k][:tag])")
            end
            println("Arithmetic operations in GB computation:            $(arit_ops_groebner)")
            println("Arithmetic operations in module overhead:           $(arit_ops_module)")
            println("Arithmetic operations in interreduction:            $(arit_ops_interred)")
            println("Size of interreduction matrix:                      $((interred_mat_size_rows, interred_mat_size_cols))")
            println("Number of zero reductions:              $(num_zero_red)")
            println("-----")
        end
        println("total arithmetic operations (groebner):        $(num_arit_operations_groebner)")
        println("total arithmetic operations (module overhead): $(num_arit_operations_module_overhead)")
        println("total arithmetic operations (interreduction):  $(num_arit_operations_interreduction)")
        verbose_saturate && println("saturation added $(global_zero_red_count) elements not in the original ideal.")
    end
    total_num_arit_ops = num_arit_operations_groebner + num_arit_operations_module_overhead + num_arit_operations_interreduction
    
    G, non_zero_cond, total_num_arit_ops
end

function f5(I::Vector{P};
            start_gen = 1,
            trace_sig_tail_tags = Symbol[],
            mod_order=:POT,
            mon_order=:GREVLEX,
            index_type=UInt32,
            mask_type=UInt32,
            pos_type=UInt32,
            select = :deg_and_pos,
            verbose = false,
            interreduction = true,
            max_remasks = 3,
            kwargs...) where {P <: AA.MPolyElem}

    R = parent(first(I))
    dat = f5setup(I, mod_order = mod_order,
                  mon_order = mon_order, index_type = index_type,
                  mask_type = mask_type, pos_type = pos_type,
                  trace_sig_tail_tags = trace_sig_tail_tags,
                  max_remasks = max_remasks, kwargs...)
    G, H, pairs = pairs_and_basis(dat, length(I), start_gen = start_gen)
    G, _, total_num_arit_ops = f5core!(dat, G, H, pairs, select = select, interreduction = interreduction, verbose = verbose)
    if verbose
        println("F5-----")
        println("final number of arithmetic operations (total):        $(total_num_arit_ops)")
        println("F5-----")
    end
    [R(dat.ctx, (i, g[1])) for i in keys(G) for g in G[i]]
end


# we have two decomposition functions for testing purposes, the ''simple''
# and the ''fancy'' loop
function naive_decomp(I::Vector{P};
                      start_gen = 1,
                      mod_order=:POT,
                      mon_order=:GREVLEX,
                      index_type=UInt32,
                      mask_type=UInt32,
                      pos_type=UInt32,
                      select = :deg_and_pos,
                      verbose = false,
                      interreduction = true,
                      max_remasks = 3,
                      kwargs...) where {P <: AA.MPolyElem}
    
    R = parent(first(I))
    dat = f5setup(I, mod_order = mod_order,
                  mon_order = mon_order, index_type = index_type,
                  mask_type = mask_type, pos_type = pos_type,
                  trace_sig_tail_tags = [:f],
                  max_remasks = max_remasks, kwargs...)
    G, H, pairs = pairs_and_basis(dat, length(I), start_gen = start_gen)
    G, _, total_num_arit_ops = f5core!(dat, G, H, pairs, select = select, verbose = verbose,
                                       new_elems = new_elems_decomp!, select_both = false,
                                       interreduction = interreduction)
    verbose && println("final number of arithmetic operations (total):        $(total_num_arit_ops)")
    [R(dat.ctx, (i, g[1])) for i in keys(G) for g in G[i]]
end

function decompose(I::Vector{P};
                   start_gen = 1,
                   mod_order=:POT,
                   mon_order=:GREVLEX,
                   index_type=UInt32,
                   mask_type=UInt32,
                   pos_type=UInt32,
                   select = :deg_and_pos,
                   verbose = false,
                   interreduction = true,
                   max_remasks = 3,
                   kwargs...) where {P <: AA.MPolyElem}
    
    R = parent(first(I))
    dat = f5setup(I, mod_order = mod_order,
                  mon_order = mon_order, index_type = index_type,
                  mask_type = mask_type, pos_type = pos_type,
                  trace_sig_tail_tags = [:f, :g_prime],
                  max_remasks = max_remasks, kwargs...)
    G, H, pairs = pairs_and_basis(dat, length(I), start_gen = start_gen)
    G, non_zero_cond, total_num_arit_ops = f5core!(dat, G, H, pairs, select = select, verbose = verbose,
                                                   new_elems = new_elems_decomp!, select_both = false,
                                                   interreduction = interreduction)

    sort!(non_zero_cond, by = p -> leadingmonomial(p), lt = (m1, m2) -> degree(dat.ctx.po.mo, m1) < degree(dat.ctx.po.mo, m2))
    verbose && println("adding $(length(non_zero_cond)) non-zero conditions...")
    dat.trace_sig_tail_tags = [:f]
    num_arit_ops_cleanup = 0
    for h in non_zero_cond
        G, H, num_arit_ops = saturate(dat, G, H, h, verbose = verbose)
        num_arit_ops_cleanup += num_arit_ops
    end
    total_num_arit_ops += num_arit_ops_cleanup
    if verbose
        println("Decompose-----")
        println("final number of arithmetic operations (core loop):    $(total_num_arit_ops - num_arit_ops_cleanup)")
        println("final number of arithmetic operations (cleanup step): $(num_arit_ops_cleanup)")
        println("final number of arithmetic operations (total):        $(total_num_arit_ops)")
        println("Decompose-----")
    end
    [R(dat.ctx, (i, g[1])) for i in keys(G) for g in G[i]]
end


function saturate(dat::F5Data{I, SΓ},
                  G::Basis{I, M},
                  H::Syz{I, M},
                  pol::Polynomial{M, T};
                  verbose = false) where {I, M, T, SΓ <: SigPolynomialΓ{I, M, T}}

    ctx = dat.ctx
    dummy_info_hashmap = Dict{I, Info}()
    dat.trace_sig_tail_tags = [:f]
    max_pos = maximum(i -> ctx.ord_indices[i][:position], keys(G))
    new_pos_key = maximum(keys(ctx.ord_indices)) + one(I)
    new_gen!(ctx, dummy_info_hashmap, max_pos + one(I), zero(I), :f, pol)
    
    pairs = pairset(ctx)
    new_sig = (new_pos_key, one(ctx.po.mo))
    G[new_pos_key] = Tuple{M, M}[]
    H[new_pos_key] = M[]
    pair!(ctx, pairs, new_sig)

    G, stuff, num_arit_ops = f5core!(dat, G, H, pairs, verbose = verbose,
                                     new_elems = new_elems_decomp!, select_both = false,
                                     saturate = true)
    G, H, num_arit_ops
end
end
