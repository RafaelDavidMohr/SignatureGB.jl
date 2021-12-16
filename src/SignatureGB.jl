module SignatureGB

const Info = Dict{String, Int}
new_info() = Dict([("arit_ops_groebner", 0),
                   ("arit_ops_module", 0),
                   ("arit_ops_interred", 0),
                   ("interred_mat_size_rows", 0),
                   ("interred_mat_size_cols", 0),
                   ("num_zero_red", 0),
                   ("max_deg_reached", 0),
                   ("gb_size_bef_interred", 0),
                   ("gb_size_aft_interred", 0)])

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
                 cleanup_at_end = true,
                 verbose = 0) where {I, M, SΓ <: SigPolynomialΓ{I, M}}
    
    ctx = dat.ctx
    R = dat.R
    use_max_sig = (select == :deg_and_pos || select == :pos)
    orig_length = length(ctx.ord_indices)

    info_hashmap = Dict([(i, new_info()) for i in keys(ctx.ord_indices)])
    mat_cnt = 0
    global_zero_red_count = 0
    verbose_stats = verbose > 0
    verbose_mat = verbose > 1
    
    curr_pos = pos(ctx, first(pairs)[1])
    curr_pos_key = first(pairs)[1][2][1]
    curr_tag = gettag(ctx, first(pairs)[1])

    non_zero_cond = Dict([(posit_key, 0) for posit_key in keys(ctx.ord_indices)])

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
            f_key = ctx.ord_indices[curr_pos_key][:att_key]
            if curr_tag == :g_gen
                non_zero_cond_local_sigs = H[curr_pos_key]
                non_zero_cond_local = eltype(ctx.po)[]
                for m in non_zero_cond_local_sigs
                    sig = (curr_pos_key, m)
                    try
                        push!(non_zero_cond_local, project(ctx, (curr_pos_key, m)))
                    catch
                        continue
                    end
                end
                if !(isempty(non_zero_cond_local))
                    h = random_lin_comb(ctx.po, non_zero_cond_local)
                    non_zero_pos = ctx.ord_indices[f_key][:position] + I(1 + non_zero_cond[f_key])
                    new_gen!(ctx, info_hashmap, non_zero_pos, curr_pos_key, :h, h)
                    non_zero_sig = (maximum(keys(ctx.ord_indices)), one(ctx.po.mo))
                    non_zero_cond[f_key] += 1
                    G[non_zero_sig[1]] = Tuple{M, M}[]
                    H[non_zero_sig[1]] = M[]
                    pair!(ctx, pairs, non_zero_sig)
                end
            end

            # prepare for the additional cleanup needed at the end
            if curr_tag == :h
                G[curr_pos_key] = Tuple{M, M}[]
                if cleanup_at_end
                    if !(ctx.ord_indices[curr_pos_key][:done]) && f_left(ctx, curr_pos)
                        inf = ctx.ord_indices[curr_pos_key]
                        ctx.ord_indices[curr_pos_key] = (position = maxpos(ctx) + one(I),
                                                         att_key = inf[:att_key],
                                                         tag = inf[:tag],
                                                         done = true)
                        pair!(ctx, pairs, (curr_pos_key, one(ctx.po.mo)))
                    end
                end
            end

            # interreducing
            info_hashmap[curr_pos_key]["gb_size_bef_interred"] = gb_size(ctx, G)
            if interreduction && indx > 2
                verbose_mat && println("-----")
                verbose_mat && println("INTERREDUCING")
                G, arit_ops, mat_size = interreduce(ctx, G, H, verbose = verbose_mat)
                info_hashmap[curr_pos_key]["arit_ops_interred"] += arit_ops
                info_hashmap[curr_pos_key]["interred_mat_size_rows"] = mat_size[1]
                info_hashmap[curr_pos_key]["interred_mat_size_cols"] = mat_size[2]
                verbose_mat && println("-----")
            end
            info_hashmap[curr_pos_key]["gb_size_aft_interred"] = gb_size(ctx, G)
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
        if curr_tag == :h
            global_zero_red_count += zero_red_count
        end

        #- PAIR GENERATION -#
        pair_gen_dat = @timed new_elems(ctx, mat, pairs, G, H, info_hashmap,
                                        enable_lower_pos_rewrite = !(interreduction))
        pairs = pair_gen_dat.value
        pair_gen_time = pair_gen_dat.time

        #- PRINTING INFORMATION -#
        if verbose_mat
            mat_cnt += 1
            println("selected $(nselected) / $(total_num_pairs) pairs, in position $(curr_pos), tagged $(curr_tag), sig-degree of sel. pairs: $(sig_degree)")
            println("symbolic pp took $(symbolic_pp_time) secs.")
            println("Matrix $(mat_cnt): $(reduction_dat.time) secs reduction / size = $(mat_size) / density = $(mat_dens)")
            if !(iszero(zero_red_count))
                println("$(zero_red_count) zero reductions at sig-degree $(sig_degree) / position $(curr_pos)")
            end
            verbose_mat && println("Pair generation took $(pair_gen_time) seconds.")
        end
    end

    verbose_mat && println("-----")

    if ctx.ord_indices[curr_pos_key][:tag] == :h
        G[curr_pos_key] = Tuple{M, M}[]
    end

    # interreducing
    if interreduction
        verbose_mat && println("FINAL INTERREDUCTION STEP")
        info_hashmap[curr_pos_key]["gb_size_bef_interred"] = gb_size(ctx, G)
        G, arit_ops, mat_size = interreduce(ctx, G, H, verbose = verbose_mat)
        info_hashmap[curr_pos_key]["interred_mat_size_rows"] = mat_size[1]
        info_hashmap[curr_pos_key]["interred_mat_size_cols"] = mat_size[2]
        info_hashmap[curr_pos_key]["arit_ops_interred"] += arit_ops
        info_hashmap[curr_pos_key]["gb_size_aft_interred"] = gb_size(ctx, G)
    end

    #- PRINTING INFORMATION -#
    verbose_stats && println("-----")
    num_arit_operations_groebner = 0
    num_arit_operations_module_overhead = 0
    num_arit_operations_interreduction = 0
    num_arit_operations_cleanup = 0
    kys = sort(collect(keys(info_hashmap)), by = k -> ctx.ord_indices[k][:position])
    for k in kys
        info = info_hashmap[k]
        arit_ops_groebner = info["arit_ops_groebner"]
        arit_ops_module = info["arit_ops_module"]
        arit_ops_interred = info["arit_ops_interred"]
        interred_mat_size_rows = info["interred_mat_size_rows"]
        interred_mat_size_cols = info["interred_mat_size_cols"]
        num_zero_red = info["num_zero_red"]
        gb_size_bef_interred = info["gb_size_bef_interred"]
        gb_size_aft_interred = info["gb_size_aft_interred"]
        max_degree = info["max_deg_reached"]
        generator_poly = ctx((k, one(ctx.po.mo)))[:poly]
        isempty(generator_poly.mo) ? deg = -1 : deg = degree(ctx.po, generator_poly)
        num_arit_operations_groebner += arit_ops_groebner
        num_arit_operations_module_overhead += arit_ops_module
        num_arit_operations_interreduction += arit_ops_interred
        if ctx.ord_indices[k][:tag] in [:h, :p, :p_gen]
            num_arit_operations_cleanup += (arit_ops_groebner + arit_ops_interred + arit_ops_module)
        end
        if verbose_stats
            if k <= orig_length
                println("INFO for index $(ctx.ord_indices[k][:position]), original index $(k), tagged $(ctx.ord_indices[k][:tag]), degree $(deg)")
            else
                println("INFO for index $(ctx.ord_indices[k][:position]), tagged $(ctx.ord_indices[k][:tag]), degree $(deg)")
            end
            println("Arithmetic operations in GB computation:              $(arit_ops_groebner)")
            println("Arithmetic operations in module overhead:             $(arit_ops_module)")
            println("Arithmetic operations in interreduction:              $(arit_ops_interred)")
            println("Size of interreduction matrix:                        $((interred_mat_size_rows, interred_mat_size_cols))")
            println("GB size before interreduction:                        $(gb_size_bef_interred)")
            println("GB size after interreduction:                         $(gb_size_aft_interred)")
            println("Maximal degree reached:                               $(max_degree)")
            println("Number of zero reductions:                            $(num_zero_red)")
            println("-----")
        end
    end
    if verbose_stats
        total_num_arit_ops = num_arit_operations_groebner + num_arit_operations_module_overhead + num_arit_operations_interreduction
        println("total arithmetic operations (groebner):               $(num_arit_operations_groebner)")
        println("total arithmetic operations (module overhead):        $(num_arit_operations_module_overhead)")
        println("total arithmetic operations (interreduction):         $(num_arit_operations_interreduction)")
        println("final number of arithmetic operations (core loop):    $(total_num_arit_ops - num_arit_operations_cleanup)")
        println("final number of arithmetic operations (cleanup step): $(num_arit_operations_cleanup)")
        println("final number of arithmetic operations (total):        $(total_num_arit_ops)")
        println("final size of GB:                                     $(gb_size(dat.ctx, G))")
    end
    verbose_stats && println("saturation added $(global_zero_red_count) elements not in the original ideal.")
    total_num_arit_ops = num_arit_operations_groebner + num_arit_operations_module_overhead + num_arit_operations_interreduction
    
    G, total_num_arit_ops
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
            verbose = 0,
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
    G, total_num_arit_ops = f5core!(dat, G, H, pairs, select = select, interreduction = interreduction, verbose = verbose)
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
                   cleanup_at_end = true,
                   verbose = 0,
                   interreduction = true,
                   max_remasks = 3,
                   kwargs...) where {P <: AA.MPolyElem}
    
    R = parent(first(I))
    dat = f5setup(I, mod_order = mod_order,
                  mon_order = mon_order, index_type = index_type,
                  mask_type = mask_type, pos_type = pos_type,
                  trace_sig_tail_tags = [:f, :g_gen, :h],
                  max_remasks = max_remasks, kwargs...)
    G, H, pairs = pairs_and_basis(dat, length(I), start_gen = start_gen)
    G, total_num_arit_ops = f5core!(dat, G, H, pairs, select = select, verbose = verbose,
                                    new_elems = new_elems_decomp!, select_both = false,
                                    cleanup_at_end = cleanup_at_end, interreduction = interreduction)
    [R(dat.ctx, (i, g[1])) for i in keys(G) for g in G[i]]
end


function saturate(dat::F5Data{I, SΓ},
                  G::Basis{I, M},
                  H::Syz{I, M},
                  pol::Polynomial{M, T};
                  verbose = 0) where {I, M, T, SΓ <: SigPolynomialΓ{I, M, T}}

    ctx = dat.ctx
    dummy_info_hashmap = Dict{I, Info}()
    dat.trace_sig_tail_tags = [:f]
    max_pos = maximum(i -> ctx.ord_indices[i][:position], keys(G))
    new_pos_key = maximum(keys(ctx.ord_indices)) + one(I)
    new_gen!(ctx, dummy_info_hashmap, max_pos + one(I), zero(I), :h, pol)
    
    pairs = pairset(ctx)
    new_sig = (new_pos_key, one(ctx.po.mo))
    G[new_pos_key] = Tuple{M, M}[]
    H[new_pos_key] = M[]
    pair!(ctx, pairs, new_sig)

    G, stuff, num_arit_ops = f5core!(dat, G, H, pairs, verbose = verbose,
                                     new_elems = new_elems_decomp!, select_both = false)
    G, H, num_arit_ops
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
                      verbose = 0,
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
    verbose > 0 && println("final number of arithmetic operations (total):        $(total_num_arit_ops)")
    [R(dat.ctx, (i, g[1])) for i in keys(G) for g in G[i]]
end
end
