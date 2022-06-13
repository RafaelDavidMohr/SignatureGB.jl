module SignatureGB
using Combinatorics

include("./useful.jl")
include("./context.jl")
include("./termorder.jl")
include("./polynomials.jl")
include("./sgbtree.jl")
include("./coefficients.jl")
include("./monomialtable.jl")
include("./sigtable.jl")
include("./logging.jl")
include("./pairs.jl")
include("./symbolicpp.jl")
include("./reduction_better.jl")
include("./gen_example_file.jl")

export sgb, f5sat, nondegen_part

# build initial pairset, basis and syzygies
function pairs_and_basis(ctx::SigPolynomialΓ,
                         basis_length;
                         start_gen = 1,
                         kwargs...)

    G = new_basis(ctx)
    for i in 1:(start_gen - 1)
        lm = leadingmonomial(ctx, unitvector(ctx, i))
        new_basis_elem!(G, unitvector(ctx, i), lm)
    end
    H = new_syz(ctx)
    pairs = pairset(ctx)
    [pair!(ctx, pairs, unitvector(ctx, i)) for i in start_gen:basis_length]
    G, H, koszul_queue(ctx), pairs
end

function sgb(I::Vector{P};
             verbose = 0,
             kwargs...) where {P <: AA.MPolyElem}

    ctx = setup(I; kwargs...)
    R = parent(first(I))
    G, H, koszul_q, pairs = pairs_and_basis(ctx, length(I); kwargs...)
    logger = SGBLogger(ctx, verbose = verbose; kwargs...)
    with_logger(logger) do
        sgb_core!(ctx, G, H, koszul_q, pairs, R; kwargs...)
        verbose == 2 && printout(logger)
    end
    [R(ctx, g) for g in G.sigs]
end

function f5sat(I::Vector{P},
               to_sat::Vector{P};
               verbose = 0,
               kwargs...) where {P<:AA.MPolyElem}

    R = parent(first(I))
    ctx = setup(I; mod_rep_type = :highest_index,
                track_module_tags = [],
                kwargs...)
    sat_tag = Symbol[]
    for (i, f) in enumerate(to_sat)
        new_generator!(ctx, length(I) + i, ctx.po(f), Symbol("to_sat_$(i)"))
        push!(sat_tag, Symbol("to_sat_$(i)"))
        push!(ctx.track_module_tags, Symbol("to_sat_$(i)"))
    end
    G, H, koszul_q, pairs = pairs_and_basis(ctx, length(I) + length(to_sat); kwargs...)
    logger = SGBLogger(ctx, verbose = verbose, task = :sat; kwargs...)
    with_logger(logger) do
        f5sat_core!(ctx, G, H, koszul_q, pairs, R, sat_tag = sat_tag; kwargs...)
        verbose == 2 && printout(logger)
    end
    [R(ctx, g) for g in G.sigs]
    # [R(ctx, g) for g in filter(g -> index(ctx, g) != maxindex(ctx), G.sigs)]
end

function f5sat_by_multiple(I::Vector{P},
                           to_sat::Vector{P};
                           verbose = 0,
                           kwargs...) where {P<:AA.MPolyElem}
    
    R = parent(first(I))
    ctx = setup(I; mod_rep_type = :highest_index,
                track_module_tags = [],
                kwargs...)
    to_sat_index_keys = pos_type(ctx)[]
    for (i, f) in enumerate(to_sat)
        new_key = new_generator!(ctx, length(I) + i, ctx.po(f), Symbol("to_sat_$(i)"))
        push!(to_sat_index_keys, new_key)
        push!(ctx.track_module_tags, Symbol("to_sat_$(i)"))
    end
    G, H, koszul_q, pairs = pairs_and_basis(ctx, length(I) + length(to_sat), start_gen = length(I) + 1; kwargs...)
    logger = SGBLogger(ctx, verbose = verbose, task = :sat; kwargs...)
    with_logger(logger) do
        components = f5sat_by_multiple_core!(ctx, G, H, koszul_q, to_sat_index_keys, R; kwargs...)
        verbose == 2 && printout(logger)
        return [[R(ctx, g) for g in G.sigs] for G in components]
    end
end

function nondegen_part(I::Vector{P};
                       verbose = 0,
                       kwargs...) where {P <: AA.MPolyElem}

    R = parent(first(I))
    if length(I) > Singular.nvars(parent(first(I)))
        error("Put in a number of polynomials less than or equal to the number of variables")
    end
    ctx = setup([I[1]]; mod_rep_type = :highest_index,
                mod_order = :POT,
                track_module_tags = [:f, :h, :zd],
                kwargs...)
    G, H, koszul_q, _ = pairs_and_basis(ctx, 1, start_gen = 2)
    remaining = [ctx.po(f) for f in I[2:end]]
    logger = SGBLogger(ctx, verbose = verbose, task = :sat; kwargs...)
    with_logger(logger) do
	result = nondegen_part_core!(ctx, G, H, koszul_q, remaining, R; kwargs...)
        verbose == 2 && printout(logger)
        [[R(ctx, sig) for sig in component.sigs] for component in result]
    end
end

function sgb_core!(ctx::SΓ,
                   G::Basis{I, M},
                   H::Syz{I, M},
                   koszul_q::KoszulQueue{I, M, SΓ},
                   pairs::PairSet{I, M, SΓ},
                   R;
                   select = nothing,
                   all_koszul = false,
                   f5c = false,
                   deg_bound = 0,
                   exit_upon_zero_reduction = false,
                   kwargs...) where {I, M, SΓ <: SigPolynomialΓ{I, M}}

    if !(extends_degree(termorder(ctx.po.mo)))
        error("I currently don't know how to deal with non-degree based monomial orderings...")
    end

    if all_koszul
        if !(mod_order(ctx) in [:POT, :DPOT])
            error("checking against all Koszul syzygies currently only supported for position over term.")
        end
    end
    
    if mod_order(ctx) == :POT 
        select = :deg_and_pos
    elseif mod_order(ctx) == :DPOT
        select = :schrey_deg_and_pos
    elseif mod_order(ctx) == :SCHREY
        select = :schrey_deg
    end

    if deg_bound > 0 && mod_order(ctx) != :DPOT
        error("only put deg_bound > 0 if you use :DPOT as a module order")
    end

    if f5c
        typeof(R) != Singular.PolyRing{n_Zp} && error("f5c currently only works with singular rings.")
        !(all_koszul) && error("Something is currently breaking when using f5c and not checking against all koszul syzygies. We are working hard to fix it :-)")
        mod_order(ctx) != :POT && error("F5c only makes sense for position over term ordering.")
    end

    # TEMP: temporary solution to not correctly symbolically preproc. the unit vectors
    # TODO: get rid of this somehow
    select_both = false

    curr_indx = index(ctx, first(pairs)[1])
    old_gb_length = length(G)
    
    while !(isempty(pairs))
        if deg_bound > 0
            deg = schrey_degree(ctx, first(pairs)[1])
            deg > deg_bound && return
        end
        next_index = index(ctx, first(pairs)[1])
        if next_index != curr_indx
            # final interreduction outside of this function
            if f5c
                if length(G) > old_gb_length
                    interreduction!(ctx, G, R)
                end
                old_gb_length = length(G)
            end
            curr_indx = next_index
        end
        
        remask!(ctx.po.mo.table)
        mat = core_loop!(ctx, G, H, koszul_q, pairs, select, all_koszul, curr_indx,
                         f5c = f5c, select_both = select_both)
        
        new_elems!(ctx, G, H, pairs, mat, all_koszul, curr_indx, f5c = f5c)
        @logmsg Verbose2 "" end_time_core = time()
        @logmsg Verbose2 "" gb_size = gb_size(ctx, G)
    end
    f5c && interreduction!(ctx, G, R)
end

function f5sat_core!(ctx::SΓ,
                     G::Basis{I,M},
                     H::Syz{I,M},
                     koszul_q::KoszulQueue{I,M,SΓ},
                     pairs::PairSet{I,M,SΓ},
                     R;
                     sat_tag = [:to_sat],
                     f5c = false,
                     deg_bound = 0,
                     excluded_tags = Symbol[],
                     excluded_index_keys = I[],
                     kwargs...) where {I,M,SΓ<:SigPolynomialΓ{I,M}}

    mod_order(ctx) != :POT && error("The experimental modifications will currently only work with POT")
    
    if !(extends_degree(termorder(ctx.po.mo)))
        error("I currently don't know how to deal with non-degree based monomial orderings...")
    end

    if mod_order(ctx) == :POT 
        select = :deg_and_pos
    elseif mod_order(ctx) == :DPOT
        select = :schrey_deg_and_pos
    end

    if f5c
        mod_order(ctx) != :POT && error("F5c only makes sense for position over term ordering.")
    end

    if deg_bound > 0 && mod_order(ctx) != :DPOT
        error("only put deg_bound > 0 if you use :DPOT as a module order")
    end
    
    all_koszul = true
    curr_indx = index(ctx, first(pairs)[1])
    curr_indx_key = first(pairs)[1][2][1]
    old_gb_length = length(G)
    
    while !(isempty(pairs))
        # TODO: is this a good idea? -> move this into sigpolynomialctx
        remask!(ctx.po.mo.table)

        next_index = index(ctx, first(pairs)[1])
        if next_index != curr_indx
            # final interreduction outside of this function
            if f5c
                if length(G) > old_gb_length
                    interreduction!(ctx, G, R)
                end
                old_gb_length = length(G)
            end
            curr_indx = next_index
            curr_indx_key = first(pairs)[1][2][1]
        end

        mat = core_loop!(ctx, G, H, koszul_q, pairs, select, all_koszul, curr_indx, select_both = false, f5c = f5c)


        @logmsg Verbose2 "" nz_entries = sum([length(row) for row in values(mat.rows)]) mat_size = (length(mat.rows), length(mat.tbl))
        new_elems!(ctx, G, H, pairs, mat, all_koszul, curr_indx, f5c = f5c; kwargs...)
        @logmsg Verbose2 "" gb_size = gb_size(ctx, G)
        
        max_sig = last(mat.sigs)
        @logmsg Verbose2 "" indx = index(ctx, max_sig) tag = tag(ctx, max_sig)
        if tag(ctx, max_sig) in sat_tag
            zero_red_row_indices = findall(row -> iszero(row), mat.rows)
            filter!(i -> tag(ctx, mat.sigs[i]) in sat_tag, zero_red_row_indices)
            if !(isempty(zero_red_row_indices))
                # zero divisors to insert
                pols_to_insert = (i -> unindexpolynomial(mat.module_tbl, mat.module_rows[i])).(zero_red_row_indices)
                insert_data = (i -> (unindexpolynomial(mat.module_tbl, mat.module_rows[i]), index(ctx, mat.sigs[i]))).(zero_red_row_indices)
                min_new_index = minimum(p_and_index -> p_and_index[2], insert_data)
                # cache some reduction results for future use
                for g in G.sigs
                    index(ctx, g[1]) >= min_new_index && push!(ctx.cashed_sigs, g)
                end

                # insert the zero divisors
                for (p, indx) in insert_data
                    # could be something like new_generator!(ctx, before current equation, p, :zd)
                    new_index_key = new_generator!(ctx, indx, p, :zd)
                    if isunit(ctx.po, p)
                        new_basis_elem!(G, unitvector(ctx, new_index_key), one(ctx.po.mo))
                        return
                    end
                end
                # syz_signatures = [g[2] for g in filter(g -> g[1] == curr_index_key, G)]

                # rebuild pairset and basis
                collected_pairset = collect(pairs)
                empty!(pairs)
                # filter stuff out of basis that might reduce further with the new generators
                filter_less_than_index!(ctx, G, min_new_index)
                # rebuild pairset
                for index_key in keys(ctx.f5_indices)
                    sig = unitvector(ctx, index_key)
                    if index(ctx, sig) >= min_new_index && !(tag(ctx, sig) in excluded_tags) && !(index_key in excluded_index_keys)
                        pair!(ctx, pairs, sig)
                    end
                end
                # preserve the pairs for which the generators are not thrown out
                for pair in collected_pairset
                    if index(ctx, pair[1]) < min_new_index
                        push!(pairs, pair)
                    end
                end
                curr_indx_key = first(pairs)[1][2][1]
            end
        end
        @logmsg Verbose2 "" end_time_core = time()
    end
end

function f5sat_by_multiple_core!(ctx::SΓ,
                                 G::Basis{I,M},
                                 H::Syz{I,M},
                                 koszul_q::KoszulQueue{I,M,SΓ},
                                 index_keys::Vector{I},
                                 R;
                                 zero_divisor_tag = :zd,
                                 kwargs...) where {I,M,SΓ<:SigPolynomialΓ{I,M}}

    # Careful: this modifies index_keys
    isempty(index_keys) && return [G]
    pairs = pairset(ctx)
    superflous = Int[]
    components = [G]
    # TODO: sort by degree?
    for (i, to_sat) in enumerate(index_keys)
        # first round: compute (I + g) and (I : g)
        @assert tag(ctx, to_sat) in ctx.track_module_tags
        pair!(ctx, pairs, unitvector(ctx, to_sat))
        isempty(pairs) && continue
        sgb_core!(ctx, components[i], H, koszul_q, pairs, R, all_koszul = true; kwargs...)

        copy_of_to_sat_key = i == length(index_keys) ? to_sat : copy_index!(ctx, to_sat)
        
        if i != length(index_keys)
            new_component = copy(components[i])
            push!(components, new_component)
        end
        filter_less_than_index!(ctx, components[i], index(ctx, to_sat))
        
        zero_divisor_sigs = filter(sig -> sig[1] == to_sat, H)
        # TODO: make the zero divisor insertion a function
        for sig in zero_divisor_sigs
            p = project(ctx, sig; kwargs...)
            new_key = new_generator!(ctx, index(ctx, to_sat), p, zero_divisor_tag)
            new_basis_elem!(components[i], unitvector(ctx, new_key), leadingmonomial(p))
        end
        # TODO: this might break things: might use later a reducer with syzygy signature?
        filter!(sig -> sig[1] != to_sat, H)
        
        while true
            empty!(pairs)
            pair!(ctx, pairs, unitvector(ctx, copy_of_to_sat_key))
            # TODO: this is not a good way to check whether 1 is contained in the ideal
            if isempty(pairs)
                push!(superflous, i)
                break
            end
            sgb_core!(ctx, components[i], H, koszul_q, pairs, R, all_koszul = true; kwargs...)
            filter_less_than_index!(ctx, components[i], index(ctx, copy_of_to_sat_key))
            zero_divisor_sigs = filter(sig -> sig[1] == copy_of_to_sat_key, H)
            isempty(zero_divisor_sigs) && break
            for sig in zero_divisor_sigs
                p = project(ctx, sig; kwargs...)
                new_key = new_generator!(ctx, index(ctx, to_sat), p, zero_divisor_tag)
                new_basis_elem!(components[i], unitvector(ctx, new_key), leadingmonomial(p))
            end
            filter!(sig -> sig[1] != copy_of_to_sat_key, H)
            @assert is_gb([R(ctx, sig) for sig in components[i].sigs])
        end
        index_keys[i] = copy_of_to_sat_key
    end
    # deleteat!(index_keys, superflous)
    return components
end

function nondegen_part_core!(ctx::SΓ,
                             G::Basis{I, M},
                             H::Syz{I, M},
                             koszul_q::KoszulQueue{I, M, SΓ},
                             remaining::Vector{P},
                             R;
                             kwargs...) where {I, M, SΓ <: SigPolynomialΓ{I, M},
                                               P <: Polynomial{M}}

    ngens = length(ctx.f5_indices)
    # non_zero_conditions = eltype(ctx)[]
    non_zero_conditions = Vector{I}[]
    pairs = pairset(ctx)
    result = [G]

    for (i, f) in enumerate(remaining)
        for component in result 
            insert_above =  maximum(g -> index(ctx, g), component.sigs)
            indx_key = new_generator!(ctx, insert_above + 1, f)
            pair!(ctx, pairs, unitvector(ctx, indx_key))
            last_index = maximum(g -> index(ctx, g), component.sigs)
            f5sat_core!(ctx, component, H, koszul_q, pairs, R,
                        sat_tag = [:f],
                        excluded_tags = [:h]; kwargs...)
            f_index = index(ctx, indx_key)
            
            newly_inserted = [key for key in keys(ctx.f5_indices) if last_index < index(ctx, key) < f_index && tag(ctx, key) == :zd]
            
            # g_h_pairs = Tuple{I, eltype(ctx.po)}[]
            
            for key in newly_inserted
                syz = filter(h -> h[1] == key, H)
                isempty(syz) && continue
                hs = [project(ctx, h) for h in syz]
                keys = [new_generator!(ctx, maxindex(ctx) + 1, cleaner, :h) for cleaner in hs]
                push!(non_zero_conditions, keys)
                println("new set of cleaners: $([R(ctx, unitvector(ctx, key)) for key in keys])")
                println("------")
                # cleaner = random_lin_comb(ctx.po, [project(ctx, h) for h in syz])
                # push!(g_h_pairs, (key, cleaner))
            end
        end

        results = Vector{typeof(G)}[]
        for component in result
            comps = [component]
            for cleaners in non_zero_conditions
                comps = vcat([f5sat_by_multiple_core!(ctx, comp, H, koszul_q, cleaners, R, zero_divisor_tag = :p; kwargs...)
                              for comp in comps]...)
            end
            push!(results, comps)
        end
        result = vcat(results...)
        filter!(component -> !(contains_unit(ctx, component)), result)
        filter!(cleaners -> !(isempty(cleaners)), non_zero_conditions)
    end
    return result    
        # check_if_contained_in = filter(sig -> index(ctx, sig) <= last_index, G.sigs)
        # for (key, cleaner) in sort(g_h_pairs, by = g_h_pair -> degree(ctx.po, g_h_pair[2]))
        #     if any(h -> iszero(poly_reduce(ctx, check_if_contained_in, R(ctx, h) * R(ctx, unitvector(ctx, key)), R)), non_zero_conditions)
        #         continue
        #     end
        #     new_indx_key = new_generator!(ctx, maxindex(ctx) + 1, cleaner, :h)
        #     push!(non_zero_conditions, unitvector(ctx, new_indx_key))
        # end
        
        # empty!(pairs)
        # f5c && interreduction!(ctx, G, R)                
    # end

    # sort!(non_zero_conditions, by = sig -> degree(ctx.po, ctx(sig).pol))
    # for cleaner in non_zero_conditions
        # new_index!(ctx, cleaner[1], maximum(g -> index(ctx, g), G.sigs) + 1, :h)
        # pair!(ctx, pairs, cleaner)
        # @assert !(isempty(pairs))
        # excluded_index_keys = [sig[1] for sig in non_zero_conditions if sig[1] != cleaner[1]]        
        # f5sat_core!(ctx, component, H, koszul_q, pairs, R,
        #             sat_tag = [:h], f5c = f5c,
    #                 excluded_index_keys = excluded_index_keys; kwargs...)
    #     empty!(pairs)
    #     filter_by_tag!(ctx, component, :h)
    #     f5c && interreduction!(ctx, component, R)
    # end

end


function core_loop!(ctx::SΓ,
                    G::Basis{I, M},
                    H::Syz{I, M},
                    koszul_q::KoszulQueue{I, M, SΓ},
                    pairs::PairSet{I, M, SΓ},
                    select,
                    all_koszul,
                    curr_indx;
                    kwargs...) where {I, M, SΓ <: SigPolynomialΓ{I, M}}
    
    @logmsg Verbose2 "" start_time_core = time()
    @logmsg Verbose1 "" curr_index = index(ctx, first(pairs)[1]) curr_index_hash = first(pairs)[1][2][1] sig_degree = degree(ctx, first(pairs)[1]) tag = tag(ctx, first(pairs)[1])
    @logmsg Verbose1 "" sugar_deg = mod_order(ctx) in [:DPOT, :SCHREY] ? sugar_deg = schrey_degree(ctx, first(pairs)[1]) : sugar_deg = -1
    @debug string("pairset:\n", [isnull(p[2]) ? "$((p[1], ctx))\n" : "$((p[1], ctx)), $((p[2], ctx))\n" for p in pairs]...)
    
    to_reduce, sig_degree, are_pairs = select!(ctx, koszul_q, pairs, Val(select), all_koszul; kwargs...)
    if isempty(to_reduce)
        return f5_matrix(ctx, easytable(M[]), easytable(M[]), Tuple{MonSigPair{I, M}, eltype(ctx.po), eltype(ctx.mod_po)}[])
    end
    
    @logmsg Verbose2 "" indx = mod_order(ctx) == :POT && !(isempty(to_reduce)) ? maximum(p -> index(ctx, p), to_reduce) : 0
    @logmsg Verbose2 "" min_deg = minimum(p -> degree(ctx.po, ctx(p...).pol), to_reduce)
    
    table, module_table, sigpolys = symbolic_pp!(ctx, to_reduce, G, H, all_koszul, curr_indx,
                                                 are_pairs = are_pairs; kwargs...)
    mat = f5_matrix(ctx, table, module_table, sigpolys)
    
    @logmsg Verbose2 "" nz_entries = sum([length(rw) for rw in mat.rows]) mat_size = (length(mat.rows), length(mat.tbl))
    
    reduction!(mat)
    return mat
end

function new_elems!(ctx::SΓ,
                    G::Basis{I, M},
                    H::Syz{I, M},
                    pairs::PairSet{I, M, SΓ},
                    mat::F5matrix,
                    all_koszul,
                    curr_indx::I;
                    kwargs...) where {I, M, SΓ <: SigPolynomialΓ{I, M}}

    for (i, (sig, row)) in enumerate(zip(mat.sigs, mat.rows))
        # @debug "considering $((sig, ctx))"
        if mod_order(ctx) == :POT
            index(ctx, sig) < curr_indx && continue
        end
        new_sig = mul(ctx, sig...)
        if isempty(row)
            #@debug "old leading monomial $(gpair(ctx.po.mo, leadingmonomial(ctx, sig..., no_rewrite = true)))"
            #@debug "syzygy $((sig, ctx))"
            @logmsg Verbose2 "" new_syz = true
            push!(H, new_sig)
            if mod_rep_type(ctx) != nothing
                q = unindexpolynomial(mat.module_tbl, mat.module_rows[i])
                ctx(new_sig, zero(q), q)
            else
                ctx(new_sig, zero(eltype(ctx.po)))
            end
            new_rewriter!(ctx, pairs, new_sig)
        else
            p = unindexpolynomial(mat.tbl, row)
            lm = leadingmonomial(p)
            #@debug "old leading monomial $(gpair(ctx.po.mo, leadingmonomial(ctx, sig..., no_rewrite = true)))"
            #@debug "new leading monomial $(gpair(ctx.po.mo, lm))"
            if (isunitvector(ctx, new_sig) && !(new_sig in G.sigs)) || lt(ctx.po.mo, lm, leadingmonomial(ctx, sig..., no_rewrite = true))
                @debug "adding $((sig, ctx))"
                @logmsg Verbose2 "" new_basis = true
                if mod_rep_type(ctx) == nothing
                    q = zero(eltype(ctx.po))
                else
                    q = unindexpolynomial(mat.module_tbl, mat.module_rows[i])
                end
                ctx(new_sig, p, q)
                new_rewriter!(ctx, pairs, new_sig)
                # TODO: adapt to new basis struct
                new_basis_elem!(G, new_sig, lm)
                pairs!(ctx, pairs, new_sig, lm, G, H, all_koszul; kwargs...)
            end
        end
    end
end

function interreduction!(ctx::SigPolynomialΓ{I, M},
                         G::Basis{I, M},
                         R) where {I, M}

    @logmsg Verbose1 "" interred = true
    basis = [R(ctx.po, ctx(g).pol) for g in G.sigs]
    interred_basis = (g -> ctx.po(g)).(gens(interreduce(Singular.Ideal(R, basis))))
    sigs = copy(G.sigs)
    empty!(G.sigs)
    sizehint!(G.sigs, length(interred_basis))
    empty!(G.lms)
    sizehint!(G.lms, length(interred_basis))
    for i in keys(G.by_index)
        empty!(G.by_index[i])
    end
    for (sig, p) in zip(sigs, interred_basis)
        ctx(sig, p)
        new_basis_elem!(G, sig, leadingmonomial(p))
    end
    @logmsg Verbose2 "" gb_size_aft_interred = gb_size(ctx, G)
end

function debug_sgb!(;io = stdout)
    no_fmt(args...) = :normal, "", ""
    logger = ConsoleLogger(io, Logging.LogLevel(-1000), meta_formatter = no_fmt)
    global_logger(logger)
    global_logger(logger)
end

end

#----- UNUSED CODE -----#

# function f45sat(I::Vector{P},
#                 to_sat::P;
#                 verbose = 0,
#                 kwargs...) where {P<:AA.MPolyElem}

#     R = parent(first(I))
#     ctx = setup(I; mod_rep_type = :highest_index,
#                 mod_order = :DPOT,
#                 track_module_tags = [:to_sat],
#                 kwargs...)
#     sat_indx_key = new_generator!(ctx, length(I) + 1, ctx.po(to_sat), :to_sat)
#     G, H, koszul_q, pairs = pairs_and_basis(ctx, length(I))
#     logger = SGBLogger(ctx, verbose = verbose, task = :f4sat; kwargs...)
#     with_logger(logger) do
#         f45sat_core!(ctx, G, H, koszul_q, pairs, R, [sat_indx_key]; kwargs...)
#         verbose == 2 && printout(logger)
#     end
#     [R(ctx, g[1]) for g in G]
# end

# function regular_limit(I::Vector{P};
#                        verbose = 0,
#                        kwargs...) where {P <: AA.MPolyElem}

#     R = parent(first(I))
#     if length(I) > Singular.nvars(parent(first(I)))
#         error("Put in a number of polynomials less than or equal to the number of variables")
#     end
#     ctx = setup(I; mod_rep_type = :random_lin_comb,
#                 mod_order = :DPOT,
#                 track_module_tags = [:f, :zd],
#                 kwargs...)
#     G, H, koszul_q, pairs = pairs_and_basis(ctx, length(I))
#     logger = SGBLogger(ctx, verbose = verbose; kwargs...)
#     with_logger(logger) do
#         regular_limit_core!(ctx, G, H, koszul_q, pairs; kwargs...)
#         verbose == 2 && printout(logger)
#     end
#     [R(ctx, g[1]) for g in G]
# end

# struct DecompResult{P}
#     result::Vector{Tuple{Vector{P}, Int64, Symbol, Symbol}}
# end

# function Base.show(io::IO, res::DecompResult)
#     for (comp, i, t, s) in res.result
#         if s == :lower_dim
#             if t == :lower_dim
#                 println(io, "component obtained on level $(i) of lower dimension coming from component of lower dimension")
#             else
#                 println(io, "component obtained on level $(i) of lower dimension coming from nondegenerate part")
#             end
#         else
#             println(io, "nondegenerate part")
#         end
#     end
# end
    
# function decomp(I::Vector{P};
#                 verbose = 0,
#                 kwargs...) where {P <: AA.MPolyElem}

#     if length(I) > Singular.nvars(parent(first(I)))
#         error("Put in a number of polynomials less than or equal to the number of variables")
#     end
#     ctx = setup([I[1]]; mod_rep_type = :highest_index,
#                 mod_order = :POT,
#                 track_module_tags = [:f, :zd],
#                 kwargs...)
#     G, H, koszul_q, _ = pairs_and_basis(ctx, 1, start_gen = 2)
#     remaining = [ctx.po(f) for f in I[2:end]]
#     logger = SGBLogger(ctx, verbose = verbose, task = :decomp)
#     with_logger(logger) do
# 	components = decomp_core!(ctx, G, H, koszul_q, remaining; kwargs...)
#         verbose == 2 && printout(logger)
#         R = parent(first(I))
#         return DecompResult([([R(ctx, g[1]) for g in G], i, t, s) for (ctx, G, i, t, s) in components])
#     end
# end

# function f45sat_core!(ctx::SΓ,
#                       G::Basis{I,M},
#                       H::Syz{I,M},
#                       koszul_q::KoszulQueue{I,M,SΓ},
#                       pairs::PairSet{I,M,SΓ},
#                       R,
#                       sat_indx_keys;
#                       max_remasks = 3,
#                       kwargs...) where {I,M,SΓ<:SigPolynomialΓ{I,M}}

#     gen_degree = indx_key -> degree(ctx.po, ctx(unitvector(ctx, indx_key)).pol)
#     deg_bound = 1
#     sat_pairset = pairset(ctx)
#     while !(isempty(pairs))
#         @logmsg Verbose2 "" add_row = true gb_or_sat = :gb
#         sgb_core!(ctx, G, H, koszul_q, pairs, R, all_koszul = true, deg_bound = deg_bound)
#         for key in sat_indx_keys
#             pair!(ctx, sat_pairset, unitvector(ctx, key))
#         end
#         if isempty(pairs)
#             deg_bound = 0
#         end
#         @logmsg Verbose2 "" add_row = true gb_or_sat = :sat
#         sgb_core!(ctx, G, H, koszul_q, sat_pairset, R, all_koszul = true, deg_bound = deg_bound,
#                   exit_upon_zero_reduction = true)
#         empty!(sat_pairset)

#         zero_divisors = [(h[1], project(ctx, h)) for h in H if h[1] in sat_indx_keys]
#         min_new_index = maxindex(ctx)
#         for (sat_indx_key, p) in zero_divisors
#             larger_deg_gen_info = filter(kv -> kv[2].tag != :to_sat && gen_degree(kv[1]) > degree(ctx.po, p),
#                                          collect(ctx.f5_indices))
#             if isempty(larger_deg_gen_info)
#                 p_index = index(ctx, sat_indx_key)
#             else
#                 p_index = minimum(kv -> kv[2].index, larger_deg_gen_info)
#             end
#             new_key = new_generator!(ctx, p_index, p, :zd)
#             if p_index < min_new_index
#                 min_new_index = p_index
#             end
#         end
#         collected_pairset = collect(pairs)
#         empty!(pairs)
#         for indx_key in keys(ctx.f5_indices)
#             if index(ctx, indx_key) >= min_new_index && tag(ctx, indx_key) != :to_sat
#                 pair!(ctx, pairs, unitvector(ctx, indx_key))
#             else
#                 for p in collected_pairset
#                     if p[1][2][1] == indx_key
#                         push!(pairs, p)
#                     end
#                 end
#             end
#         end
#         filter!(g -> index(ctx, g[1]) < min_new_index, G)
#         filter!(h -> !(h[1] in sat_indx_keys), H)
#         deg_bound += 1
#     end
# end

# function decomp_core!(ctx::SΓ,
#                       G::Basis{I, M},
#                       H::Syz{I, M},
#                       koszul_q::KoszulQueue{I, M, SΓ},
#                       remaining::Vector{P},
#                       max_remasks = 3,
#                       kwargs...) where {I, M, SΓ <: SigPolynomialΓ{I, M},
#                                         P <: Polynomial{M}}

#     ngens = length(ctx.f5_indices)
#     components = [(ctx, G, H, 1, :nondeg, :nondeg)]
    
#     for (i, f) in enumerate(remaining)
#         for (j, (ctx, G, H, l, t, s)) in enumerate(copy(components))
#             @logmsg Verbose2 "" add_row = true defaults = [(:component, j), (:level, i)]
#             indx_key = new_generator!(ctx, f)
#             pairs = pairset(ctx)
#             pair!(ctx, pairs, unitvector(ctx, indx_key))
#             last_index = maximum(g -> index(ctx, g[1]), G)
#             G_old = copy(G)
#             basis_before = [ctx(g[1]).pol for g in G_old]
#             f5sat_core!(ctx, G, H, koszul_q, pairs, max_remasks = max_remasks, sat_tag = :f; kwargs...)
#             ctx.f5_indices[indx_key].tag = :f

#             # construct components of higher dimension
#             curr_index = ctx.f5_indices[indx_key].index
#             new_components = empty(components)
#             gs = [(k, ctx(unitvector(ctx, k)).pol) for (k, v) in ctx.f5_indices
#                       if v.tag == :zd && last_index < v.index < curr_index]
#             if any(g -> isunit(ctx.po, g[2]), gs)
#                 components[j] = (ctx, G_old, H, l, t, s)
#                 continue
#             end
#             for (j, (zd_index, g)) in enumerate(gs)
#                 new_comp_pols = copy(basis_before)
#                 for k in 1:j-1
#                     push!(new_comp_pols, g)
#                 end
#                 for sig in H
#                     if sig[1] == zd_index[1]
#                         p = project(ctx, sig)
#                         push!(new_comp_pols, p)
#                     end
#                 end
#                 ctx_new = sigpolynomialctx(ctx.po.co, 0,
#                                            polynomials = ctx.po,
#                                            track_module_tags = [:f, :zd],
#                                            mod_rep_type = :highest_index)
#                 G_new = new_basis(ctx_new)
#                 H_new = new_syz(ctx_new)
#                 for (l, p) in enumerate(new_comp_pols)
#                     new_generator!(ctx_new, l, p, :f)
#                     new_basis_elem!(ctx_new, G_new, unitvector(ctx_new, l))
#                 end
#                 push!(new_components, (ctx_new, G_new, H_new, i+1, s, :lower_dim))
#             end
#             components = vcat(components, new_components)
#         end
#     end
#     return [(ctx, G, i, t, s) for (ctx, G, H, i, t, s) in components]
# end

# function regular_limit_core!(ctx::SΓ,
#                              G::Basis{I,M},
#                              H::Syz{I,M},
#                              koszul_q::KoszulQueue{I,M,SΓ},
#                              pairs::PairSet{I,M,SΓ};
#                              kwargs...) where {I, M, SΓ<:SigPolynomialΓ{I,M}}
    
#     if !(extends_degree(termorder(ctx.po.mo)))
#         error("I currently don't know how to deal with non-degree based monomial orderings...")
#     end
#     select = :schrey_deg
#     all_koszul = true

#     while !(isempty(pairs))
        
#         to_reduce, done = core_loop!(ctx, G, H, koszul_q, pairs, select, all_koszul, select_both = false; kwargs...)
#         isempty(to_reduce) && continue
#         mat = F5matrix(ctx, done, collect(to_reduce); kwargs...)
#         @logmsg Verbose2 "" nz_entries = sum([length(rw) for rw in values(rows(mat))]) mat_size = (length(rows(mat)), length(tbl(mat)))
#         reduction!(mat)
#         rws = rows(mat)

#         zero_red_all = filter(kv -> iszero(pol(mat, kv[2])), rws)
#         zero_red = filter(kv -> !(iszero(module_pol(mat, kv[1]))), zero_red_all)
#         if isempty(zero_red)
#             new_elems!(ctx, G, H, pairs, mat, all_koszul; kwargs...)
#             @logmsg Verbose2 "" gb_size = gb_size(ctx, G)
#         else
#             for (sig, _) in zero_red_all
#                 push!(H, mul(ctx, sig...))
#                 ctx(mul(ctx, sig...), zero(eltype(ctx.po)))
#             end
#             pols_to_insert = (sig -> unindexpolynomial(tbl(mat.module_matrix), module_pol(mat, sig))).(keys(zero_red))
#             max_indx = maxindex(ctx)
#             # insert zero divisors
#             println("inserting stuff")
#             for (i, p) in enumerate(pols_to_insert)
#                 @logmsg Verbose2 "" new_syz = true
#                 new_index_key = new_generator!(ctx, max_indx + i, p, :zd)
#                 if isunit(ctx.po, p)
#                     new_basis_elem!(G, unitvector(ctx, new_index_key), one(ctx.po.mo))
#                     return
#                 end
#             end
#             # rebuild basis and pairset
#             pairs = pairset(ctx)
#             filter!(g -> all(i -> lt(ctx, g[1], unitvector(ctx, max_indx + i)), 1:length(pols_to_insert)), G)
#             for i in 1:length(pols_to_insert)
#                 pair!(ctx, pairs, unitvector(ctx, max_indx + i))
#             end
#             for index_key in keys(ctx.f5_indices)
#                 if any(i -> lt(ctx, unitvector(ctx, max_indx + i), unitvector(ctx, index_key)), 1:length(pols_to_insert))
#                     pair!(ctx, pairs, unitvector(ctx, index_key))
#                 end
#             end
#         end
#         @logmsg Verbose2 "" end_time_core = time()
#     end
# end
