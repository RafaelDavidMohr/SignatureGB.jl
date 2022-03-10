module SignatureGB

include("./useful.jl")
include("./context.jl")
include("./termorder.jl")
include("./polynomials.jl")
include("./coefficients.jl")
include("./monomialtable.jl")
include("./sigtable.jl")
# include("./f5data.jl")
include("./pairs.jl")
include("./symbolicpp.jl")
include("./reduction_better.jl")
# include("./interreduction.jl")
# include("./gen_example_file.jl")

# export f5, decompose

# build initial pairset, basis and syzygies
function pairs_and_basis(ctx::SigPolynomialΓ,
                         basis_length;
                         start_gen = 1,
                         kwargs...)

    G = new_basis(ctx)
    for i in 1:(start_gen - 1)
        lm = leadingmonomial(ctx, unitvector(ctx, i))
        push!(G, ((i, one(ctx.po.mo)), lm))
    end
    H = new_syz(ctx)
    pairs = pairset(ctx)
    [pair!(ctx, pairs, unitvector(ctx, i)) for i in start_gen:basis_length]
    G, H, koszul_queue(ctx), pairs
end

# TODO: logging
function sgb(I::Vector{P};
             kwargs...) where {P <: AA.MPolyElem}

    ctx = setup(I, kwargs...)
    G, H, koszul_q, pairs = pairs_and_basis(ctx, length(I))
    sgb_core!(ctx, G, H, pairs, koszul_q, kwargs...)
    R = base_ring(first(I))
    [R(ctx, g) for g in G]
end

function sgb_core!(ctx::SΓ,
                   G::Basis{I, M},
                   H::Syz{I, M},
                   koszul_q::KoszulQueue{I, M, SΓ},
                   pairs::PairSet{I, M, SΓ};
                   select = nothing,
                   max_remasks = 3,
                   kwargs...) where {I, M, SΓ <: SigPolynomialΓ{I, M}}

    if !(extends_degree(termorder(ctx.po.mo)))
        error("I currently don't know how to deal with non-degree based monomial orderings...")
    else
        use_max_sig = true
    end

    if isnothing(select)
        if mod_order(ctx) == :POT
            select = :deg_and_pos
        elseif mod_order(ctx) == :TOP || mod_order(ctx) == :SCHREY
            select = :deg
        else
            error("Unsupported module order. Pick one of :POT, :TOP or :SCHREY")
        end
    end
        
    while !(isempty(pairs))
        # TODO: is this a good idea
        if max_remasks > 0 && rand() < max(1/max_remasks, 1/3)
            max_remasks -= 1
            remask!(ctx.po.mo.table)
        end
        to_reduce, are_pairs = select!(ctx, koszul_q, pairs, Val(select), select_both = select_both)
        done = symbolic_pp!(ctx, to_reduce, G, H, use_max_sig = use_max_sig,
                            are_pairs = are_pairs)
        mat = F5matrix(ctx, done, to_reduce)
        reduction!(mat)

        @inbounds begin
            for (sig, row) in rows(mat)
                new_sig = mul(ctx, sig...)
                if isempty(row)
                    push!(H, sig)
                    new_rewriter!(ctx, pairs, new_sig)
                else
                    p = unindexpolynomial(tbl(mat), row)
                    lm = leadingmonomial(p)
                    if lt(ctx.po.mo, lm, leadingmonomial(ctx, sig..., no_rewrite = true))
                        new_rewriter!(ctx, pairs, new_sig)
                        push!(G, new_sig)
                        pairs!(ctx, pairs, new_sig, lm, G, H)
                    end
                end
            end
        end 
    end
end

# # TODO: write this function
# function nondegenerate_locus_core!(dat::F5Data{I, SΓ},
#                                    G::Basis{I, M},
#                                    H::Syz{I, M},
#                                    pairs::PairSet{I, M, SΓ};
#                                    select = :deg_and_pos,
#                                    new_elems = new_elems_f5!,
#                                    interreduction = true,
#                                    select_both = true,
#                                    verbose = 0) where {I, M, SΓ <: SigPolynomialΓ{I, M}}
#     # dummy
#     return
# end

# function f5core!(dat::F5Data{I, SΓ},
#                  G::Basis{I, M},
#                  H::Syz{I, M},
#                  pairs::PairSet{I, M, SΓ};
#                  select = :deg_and_pos,
#                  new_elems = new_elems_f5!,
#                  interreduction = true,
#                  select_both = true,
#                  verbose = 0) where {I, M, SΓ <: SigPolynomialΓ{I, M}}
    
#     ctx = dat.ctx
#     R = dat.R
#     use_max_sig = (select == :deg_and_pos || select == :pos)
#     orig_length = length(ctx.ord_indices)

#     # PRNT: this all goes into the dat field
#     info_hashmap = Dict([(i, new_info()) for i in keys(ctx.ord_indices)])
#     mat_cnt = 0
#     global_zero_red_count = 0
#     times = timings(0.0, 0.0, 0.0)
#     verbose_stats = verbose > 0
#     verbose_mat = verbose > 1
    
#     curr_indx = index(ctx, first(pairs)[1])
#     curr_indx_key = first(pairs)[1][2][1]
#     curr_tag = tag(ctx, first(pairs)[1])

#     non_zero_cond = I[]
    
#     while !(isempty(pairs))
#         #- INTERREDUCTION -#
#         timed = @elapsed begin
#             indx = pos(ctx, first(pairs)[1])
#             if indx != curr_indx && mod_order(dat.ctx) == :POT

#                 # here we do several steps when the index jumps:
#                 # possibly remasking
#                 if dat.remasks_left > 0
#                     remask!(dat.ctx.po.mo.table)
#                     dat.remasks_left -= 1
#                 end

#                 # if we are in a decomposition computation we add non-zero conditions
#                 if curr_tag == :g_gen
#                     non_zero_cond_local_sigs = H[curr_indx_key]
#                     non_zero_cond_local = eltype(ctx.po)[]
#                     for m in non_zero_cond_local_sigs
#                         sig = (curr_indx_key, m)
#                         try
#                             push!(non_zero_cond_local, project(ctx, (curr_indx_key, m)))
#                         catch KeyError
#                             continue
#                         end
#                     end
#                     if !(isempty(non_zero_cond_local))
#                         h = random_lin_comb(ctx.po, non_zero_cond_local)
#                         new_posit_key = register!(ctx, h, info_hashmap)
#                         push!(non_zero_cond, new_posit_key)
#                     end
#                 end

#                 if curr_tag == :f
#                     for (j, i) in enumerate(non_zero_cond)
#                         new_pos!(ctx, i, curr_indx + I(j), curr_indx_key, :h)
#                         G[i] = Tuple{M, M}[]
#                         H[i] = M[]
#                         pair!(ctx, pairs, (i, one(ctx.po.mo)))
#                     end
#                 end

#                 if curr_tag == :h
#                     G[curr_indx_key] = Tuple{M, M}[]
#                 end

#                 # interreducing
#                 # PRNT: all of this needs to be done in the interreduction function
#                 info_hashmap[curr_indx_key]["gb_size_bef_interred"] = gb_size(ctx, G)
#                 if interreduction && indx > 2
#                     verbose_mat && println("-----")
#                     verbose_mat && println("INTERREDUCING")
#                     G, arit_ops, mat_size = interreduce(ctx, G, H, verbose = verbose_mat)
#                     info_hashmap[curr_indx_key]["arit_ops_interred"] += arit_ops
#                     info_hashmap[curr_indx_key]["interred_mat_size_rows"] = mat_size[1]
#                     info_hashmap[curr_indx_key]["interred_mat_size_cols"] = mat_size[2]
#                     verbose_mat && println("-----")
#                 end
#                 info_hashmap[curr_indx_key]["gb_size_aft_interred"] = gb_size(ctx, G)
#             end
#             # update current index, current tag and current index key
#             curr_indx = indx
#             curr_tag = gettag(ctx, first(pairs)[1])
#             curr_indx_key = first(pairs)[1][2][1]

#             #- PAIR SELECTION -#
#             #PRNT: Print nselected/total_num_pairs in select function
#             total_num_pairs = length(pairs)
#             to_reduce, are_pairs, nselected, sig_degree = select!(ctx, pairs, Val(select), select_both = select_both)

#             #- SYMBOLIC PP -#
#             # PRNT: timings in symbolicpp itself
#             symbolic_pp_timed  = @timed symbolic_pp!(ctx, to_reduce, G, H,
#                                                      use_max_sig = use_max_sig,
#                                                      sig_degree = sig_degree,
#                                                      max_sig_pos = curr_indx,
#                                                      are_pairs = are_pairs,
#                                                      enable_lower_pos_rewrite = !(interreduction))
#             done = symbolic_pp_timed.value
#             symbolic_pp_time = symbolic_pp_timed.time
#             # PRNT: record mat_size and mat_dens in the constructor
#             mat = f5matrix(ctx, done, collect(to_reduce), curr_indx, curr_indx_key, curr_tag,
#                            trace_sig_tail_tags = dat.trace_sig_tail_tags,
#                            enable_lower_pos_rewrite = !(interreduction))
#             mat_size = (length(rows(mat)), length(mat.tbl))
#             mat_dens = sum([length(rw) for rw in rows(mat)]) / (mat_size[1] * mat_size[2])

#             #- REDUCTION -#
#             reduction_dat = @timed reduction!(mat)

#             # storing computational information
#             # PRNT: all of this needs to be recorded in the reduction function
#             zero_red_count = length(filter(sig_rw -> isempty(sig_rw[2]), mat.sigs_rows))
#             info_hashmap[curr_indx_key]["arit_ops_groebner"] += reduction_dat.value[1]
#             info_hashmap[curr_indx_key]["arit_ops_module"] += reduction_dat.value[2]
#             info_hashmap[curr_indx_key]["num_zero_red"] += zero_red_count
#             if curr_tag == :h
#                 global_zero_red_count += zero_red_count
#             end

#             #- PAIR GENERATION AND ADDING ELEMENTS TO BASIS/SYZYGIES -#
#             # PRNT: record the metadata in the functions
#             pair_gen_dat = @timed new_elems(ctx, mat, pairs, G, H, info_hashmap, non_zero_cond,
#                                             enable_lower_pos_rewrite = !(interreduction))
#             pairs = pair_gen_dat.value
#             pair_gen_time = pair_gen_dat.time

#             #- PRINTING INFORMATION -#
#             # PRNT: Intermediate print function
#             if verbose_mat
#                 mat_cnt += 1
#                 println("selected $(nselected) / $(total_num_pairs) pairs, in position $(curr_indx), tagged $(curr_tag), sig-degree of sel. pairs: $(sig_degree)")
#                 println("symbolic pp took $(symbolic_pp_time) secs.")
#                 println("Matrix $(mat_cnt): $(reduction_dat.time) secs reduction / size = $(mat_size) / density = $(mat_dens)")
#                 if !(iszero(zero_red_count))
#                     println("$(zero_red_count) zero reductions at sig-degree $(sig_degree) / position $(curr_indx)")
#                 end
#                 verbose_mat && println("Pair generation took $(pair_gen_time) seconds.")
#             end

#             if isempty(pairs) && curr_tag == :f && !(isempty(non_zero_cond))
#                 # preparation for final cleanup
#                 for (j, i) in enumerate(non_zero_cond)
#                     new_pos!(ctx, i, curr_indx + I(j), curr_indx_key, :h)
#                     pair!(ctx, pairs, (i, one(ctx.po.mo)))
#                     G[i] = Tuple{M, M}[]
#                     H[i] = M[]
#                 end
#                 if !(isempty(pairs))
#                     # PRNT: see above for interreduction
#                     if interreduction
#                         verbose_mat && println("interreducing")
#                         info_hashmap[curr_indx_key]["gb_size_bef_interred"] = gb_size(ctx, G)
#                         G, arit_ops, mat_size = interreduce(ctx, G, H, verbose = verbose_mat)
#                         info_hashmap[curr_indx_key]["interred_mat_size_rows"] = mat_size[1]
#                         info_hashmap[curr_indx_key]["interred_mat_size_cols"] = mat_size[2]
#                         info_hashmap[curr_indx_key]["arit_ops_interred"] += arit_ops
#                         info_hashmap[curr_indx_key]["gb_size_aft_interred"] = gb_size(ctx, G)
#                     end
#                     curr_indx = pos(ctx, first(pairs)[1])
#                     curr_tag = gettag(ctx, first(pairs)[1])
#                     curr_indx_key = first(pairs)[1][2][1]
#                 end
#             end
#         end
#         # PRNT: ?
#         # Split up timings between core loop and cleanup
#         if curr_tag in [:f, :g, :g_gen]
#             times.time_core_loop += timed
#         elseif iszero(f_left(ctx, curr_indx))
#             times.time_final_clean += timed
#         else
#             times.time_intermed_clean += timed
#         end            
#     end
#     verbose_mat && println("-----")

#     if ctx.ord_indices[curr_indx_key][:tag] == :h
#         G[curr_indx_key] = Tuple{M, M}[]
#     end

#     # interreducing
#     timed = @elapsed begin
#         # PRNT: see above
#         if interreduction
#             verbose_mat && println("FINAL INTERREDUCTION STEP")
#             info_hashmap[curr_indx_key]["gb_size_bef_interred"] = gb_size(ctx, G)
#             G, arit_ops, mat_size = interreduce(ctx, G, H, verbose = verbose_mat)
#             info_hashmap[curr_indx_key]["interred_mat_size_rows"] = mat_size[1]
#             info_hashmap[curr_indx_key]["interred_mat_size_cols"] = mat_size[2]
#             info_hashmap[curr_indx_key]["arit_ops_interred"] += arit_ops
#             info_hashmap[curr_indx_key]["gb_size_aft_interred"] = gb_size(ctx, G)
#         end
#     end
#     times.time_core_loop += timed

#     #- PRINTING INFORMATION -#
#     # PRNT: all of this in seperate function
#     verbose_stats && println("-----")
#     num_arit_operations_groebner = 0
#     num_arit_operations_module_overhead = 0
#     num_arit_operations_interreduction = 0
#     num_arit_operations_cleanup = 0
#     kys = sort(collect(keys(info_hashmap)), by = k -> ctx.ord_indices[k][:position])
#     for k in kys
#         info = info_hashmap[k]
#         arit_ops_groebner = info["arit_ops_groebner"]
#         arit_ops_module = info["arit_ops_module"]
#         arit_ops_interred = info["arit_ops_interred"]
#         interred_mat_size_rows = info["interred_mat_size_rows"]
#         interred_mat_size_cols = info["interred_mat_size_cols"]
#         num_zero_red = info["num_zero_red"]
#         gb_size_bef_interred = info["gb_size_bef_interred"]
#         gb_size_aft_interred = info["gb_size_aft_interred"]
#         max_degree = info["max_deg_reached"]
#         generator_poly = ctx((k, one(ctx.po.mo)))[:poly]
#         isempty(generator_poly.mo) ? deg = -1 : deg = degree(ctx.po, generator_poly)
#         num_arit_operations_groebner += arit_ops_groebner
#         num_arit_operations_module_overhead += arit_ops_module
#         num_arit_operations_interreduction += arit_ops_interred
#         if ctx.ord_indices[k][:tag] in [:h, :p, :p_gen]
#             num_arit_operations_cleanup += (arit_ops_groebner + arit_ops_interred + arit_ops_module)
#         end
#         if verbose_stats
#             if k <= orig_length
#                 println("INFO for index $(ctx.ord_indices[k][:position]), original index $(k), tagged $(ctx.ord_indices[k][:tag]), degree $(deg)")
#             else
#                 println("INFO for index $(ctx.ord_indices[k][:position]), tagged $(ctx.ord_indices[k][:tag]), degree $(deg)")
#             end
#             println("Arithmetic operations in GB computation:              $(arit_ops_groebner)")
#             println("Arithmetic operations in module overhead:             $(arit_ops_module)")
#             println("Arithmetic operations in interreduction:              $(arit_ops_interred)")
#             println("Size of interreduction matrix:                        $((interred_mat_size_rows, interred_mat_size_cols))")
#             println("GB size before interreduction:                        $(gb_size_bef_interred)")
#             println("GB size after interreduction:                         $(gb_size_aft_interred)")
#             println("Maximal degree reached:                               $(max_degree)")
#             println("Number of zero reductions:                            $(num_zero_red)")
#             println("-----")
#         end
#     end
#     if verbose_stats
#         total_num_arit_ops = num_arit_operations_groebner + num_arit_operations_module_overhead + num_arit_operations_interreduction
#         println("total arithmetic operations (groebner):               $(num_arit_operations_groebner)")
#         println("total arithmetic operations (module overhead):        $(num_arit_operations_module_overhead)")
#         println("total arithmetic operations (interreduction):         $(num_arit_operations_interreduction)")
#         println("final number of arithmetic operations (core loop):    $(total_num_arit_ops - num_arit_operations_cleanup)")
#         println("final number of arithmetic operations (cleanup step): $(num_arit_operations_cleanup)")
#         println("final number of arithmetic operations (total):        $(total_num_arit_ops)")
#         println("final size of GB:                                     $(gb_size(dat.ctx, G))")
#         println("-----")
#         println("time spent in core loop:                              $(times.time_core_loop)")
#         println("time spent in intermediate cleanup:                   $(times.time_intermed_clean)")
#         println("time spent in final cleanup:                          $(times.time_final_clean)")
#     end

#     verbose_stats && println("saturation added $(global_zero_red_count) elements not in the original ideal.")
#     total_num_arit_ops = num_arit_operations_groebner + num_arit_operations_module_overhead + num_arit_operations_interreduction
    
#     G, total_num_arit_ops
# end

# # TODO: provide some defaults here
# function f5(I::Vector{P};
#             kwargs...) where {P <: AA.MPolyElem}

#     R = parent(first(I))
#     ctx = setup(I,kwargs...)
#     G, H, pairs = pairs_and_basis(ctx, length(I), kwargs...)
#     G, total_num_arit_ops = f5core!(ctx, G, H, pairs, kwargs...)
#     [R(dat.ctx, (i, g[1])) for i in keys(G) for g in G[i]]
# end

# # TODO: provide some defaults here
# function decompose(I::Vector{P};
#                    kwargs...) where {P <: AA.MPolyElem}
    
#     R = parent(first(I))
#     ctx = setup(I, kwargs...)
#     G, H, pairs = pairs_and_basis(dat, length(I), start_gen = start_gen)
#     G, total_num_arit_ops = nondegenerate_part_core!(dat, G, H, pairs, kwargs...)
#     [R(dat.ctx, (i, g[1])) for i in keys(G) for g in G[i]]
# end
end
