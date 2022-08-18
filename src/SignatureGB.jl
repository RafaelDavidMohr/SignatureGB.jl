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
               to_sat::P;
               verbose = 0,
               f5c = false,
               kwargs...) where {P<:AA.MPolyElem}

    R = parent(first(I))
    ctx = setup(I; mod_rep_type = :highest_index,
                track_module_tags = [:to_sat],
                kwargs...)
    G, H, koszul_q, pairs = pairs_and_basis(ctx, length(I); kwargs...)
    sat_id = new_generator!(ctx, pos_type(ctx)(length(I)), ctx.po(to_sat), :to_sat)
    pair!(ctx, pairs, unitvector(ctx, sat_id))
    logger = SGBLogger(ctx, verbose = verbose, task = :sat, f5c = f5c; kwargs...)
    S, vars = Singular.PolynomialRing(Fp(Int(characteristic(R))), ["x$(i)" for i in 1:length(gens(R))])
    with_logger(logger) do
        f5sat_core!(ctx, G, H, koszul_q, pairs, S, f5c = f5c; kwargs...)
        delete_indices!(ctx, G, [sat_id])
        if f5c
            interreduction!(ctx, G, S)
        end
        verbose == 2 && printout(logger)
    end
    [R(ctx, g) for g in G.sigs]
end

function nondegen_part(I::Vector{P};
                       verbose = 0,
                       kwargs...) where {P<:AA.MPolyElem}

    R = parent(first(I))
    if length(I) > length(gens(R))
        error("Put in a number of polynomials less or equal than the number of variables.")
    end
    ctx = setup([I[1]]; mod_rep_type = :highest_index,
                track_module_tags = [:f, :zd, :h],
                kwargs...)
    G, H, koszul_q, _ = pairs_and_basis(ctx, 1, start_gen = 2; kwargs...)
    logger = SGBLogger(ctx, verbose = verbose, task = :sat; kwargs...)

    with_logger(logger) do
        nondegen_part_core!(ctx, G, H, koszul_q, I[2:end], R; kwargs...)
        verbose == 2 && printout(logger)
    end
    [R(ctx, g) for g in G.sigs]
end
    
function sgb_core!(ctx::SΓ,
                   G::Basis{I, M},
                   H::Syz{I, M},
                   koszul_q::KoszulQueue{I, M, SΓ},
                   pairs::PairSet{I, M},
                   R;
                   select = nothing,
                   all_koszul = false,
                   f5c = false,
                   deg_bound = 0,
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
        # typeof(R) != Singular.PolyRing{n_Zp} && error("f5c currently only works with singular rings.")
        !(all_koszul) && error("Something is currently breaking when using f5c and not checking against all koszul syzygies. We are working hard to fix it :-)")
        mod_order(ctx) != :POT && error("F5c only makes sense for position over term ordering.")
    end

    S, vars = Singular.PolynomialRing(Fp(Int(characteristic(R))), ["x$(i)" for i in 1:length(gens(R))])

    # TEMP: temporary solution to not correctly symbolically preproc. the unit vectors
    # TODO: get rid of this somehow
    select_both = false

    curr_indx_key = first(pairs)[1][2][1]
    old_gb_length = length(G)
    
    while !(isempty(pairs))
        sort!(pairs, lt = (p1, p2) -> Base.Order.lt(pairordering(ctx), p1, p2))
        if deg_bound > 0
            deg = schrey_degree(ctx, first(pairs)[1])
            deg > deg_bound && return
        end
        next_index_key = first(pairs)[1][2][1]
        if next_index_key != curr_indx_key
            # final interreduction outside of this function
            if f5c
                if length(G) > old_gb_length
                    interreduction!(ctx, G, S)
                end
                old_gb_length = length(G)
            end
            curr_indx_key = next_index_key
        end
        
        remask!(ctx.po.mo.table)
        mat = core_loop!(ctx, G, H, koszul_q, pairs, select, all_koszul,
                         sort_id(ctx, curr_indx_key),
                         f5c = f5c, select_both = select_both)
        
        new_elems!(ctx, G, H, pairs, mat, all_koszul,
                   sort_id(ctx, curr_indx_key), f5c = f5c)
        @logmsg Verbose2 "" end_time_core = time()
        @logmsg Verbose2 "" gb_size = gb_size(ctx, G.sigs)
    end
    f5c && interreduction!(ctx, G, S)
end

function f5sat_core!(ctx::SΓ,
                     G::Basis{I,M},
                     H::Syz{I,M},
                     koszul_q::KoszulQueue{I,M,SΓ},
                     pairs::PairSet{I,M},
                     R;
                     sat_tag = [:to_sat],
                     zd_tag = :zd,
                     f5c = false,
                     kwargs...) where {I,M,SΓ<:SigPolynomialΓ{I,M}}

    
    if !(extends_degree(termorder(ctx.po.mo)))
        error("I currently don't know how to deal with non-degree based monomial orderings...")
    end

    select = :deg_and_pos
    all_koszul = true
    select_both = false
    
    curr_indx_key = first(pairs)[1][2][1]
    old_gb_length = length(G)
    
    while !(isempty(pairs))
        sort!(pairs, lt = (p1, p2) -> Base.Order.lt(pairordering(ctx), p1, p2))
        next_index_key = first(pairs)[1][2][1]
        if next_index_key != curr_indx_key
            # final interreduction outside of this function
            if f5c
                if length(G) > old_gb_length
                    interreduction!(ctx, G, R)
                end
                old_gb_length = length(G)
            end
            curr_indx_key = next_index_key
        end
        
        remask!(ctx.po.mo.table)       
        mat = core_loop!(ctx, G, H, koszul_q, pairs, select, all_koszul,
                         sort_id(ctx, curr_indx_key),
                         select_both = select_both, f5c = f5c)
        if !(isempty(mat.sigs))
            @logmsg Verbose2 "" tag = tag(ctx, last(mat.sigs)) indx_hash = last(mat.sigs)[2][1]
        else
            continue
        end

        new_elems!(ctx, G, H, pairs, mat, all_koszul,
                   sort_id(ctx, curr_indx_key), f5c = f5c)
        @logmsg Verbose2 "" gb_size = gb_size(ctx, G.sigs)
        
        max_sig = last(mat.sigs)
        if tag(ctx, max_sig) in sat_tag
            zero_red_row_indices = findall(row -> iszero(row), mat.rows)
            if !(isempty(zero_red_row_indices))
                # zero divisors to insert
                pols_to_insert = (i -> unindexpolynomial(mat.module_tbl, mat.module_rows[i])).(zero_red_row_indices)
                # cache some reduction results for future use
                for g in G.sigs
                    g[1] == max_sig[2][1] && push!(ctx.cashed_sigs, g)
                end

                # insert the zero divisors, rebuild pairs and basis
                empty!(pairs)
                delete_indices!(ctx, G, [max_sig[2][1]])
                for p in pols_to_insert
                    if parent_id(ctx, max_sig[2][1]) in ctx.branch_nodes
                        new_id = new_generator_before!(ctx, parent_id(ctx, max_sig[2][1]), p, zd_tag)
                    else
                        new_id = new_generator_before!(ctx, max_sig[2][1], p, zd_tag)
                    end
                    if isunit(ctx.po, p)
                        new_basis_elem!(G, unitvector(ctx, new_index_key), one(ctx.po.mo))
                        return
                    end
                    pair!(ctx, pairs, unitvector(ctx, new_id))
                end
                pair!(ctx, pairs, unitvector(ctx, max_sig[2][1]))
                curr_indx_key = first(pairs)[1][2][1]
            end
        end
        @logmsg Verbose2 "" end_time_core = time()
    end
end

function nondegen_part_core!(ctx::SΓ,
                             G::Basis{I, M},
                             H::Syz{I, M},
                             koszul_q::KoszulQueue{I, M, SΓ},
                             remaining::Vector{P},
                             R;
                             kwargs...) where {I, M, SΓ <: SigPolynomialΓ{I, M},
                                               P <: AA.MPolyElem}

    S, vars = Singular.PolynomialRing(Fp(Int(characteristic(R))), ["x$(i)" for i in 1:length(gens(R))])
    non_zero_conditions = I[]
    pairs = pairset(ctx)
    branch_node_id = first(ctx.branch_nodes)
    minimal_larger_f_id = id -> begin
        child_id = first(children_id(ctx, id))
        if tag(ctx, child_id) == :f
            child_id
        else
            minimal_larger_f_id(child_id)
        end
    end
    
    for f in remaining
        # process f
        f_id = new_generator_before!(ctx, branch_node_id, ctx.po(f))
        pair!(ctx, pairs, unitvector(ctx, f_id))
        f5sat_core!(ctx, G, H, koszul_q, pairs, S, sat_tag = [:f]; kwargs...)
        empty!(pairs)
        # extract new cleaners
        newly_inserted = filter(id -> tag(ctx, id) == :zd && minimal_larger_f_id(id) == f_id,
                                keys(ctx.sgb_nodes))
        # attach new cleaners to branch node
        for id in newly_inserted
            h = random_lin_comb(ctx.po, (sig -> project(ctx, sig)).(filter(sig -> sig[1] == id, H)))
            h_id = new_generator!(ctx, branch_node_id, h, :h)
            push!(non_zero_conditions, h_id)
        end
        # sort them by degree
        sort!(non_zero_conditions, by = id -> degree(ctx.po, ctx(unitvector(ctx, id)).pol))
        # process cleaners
        for id in non_zero_conditions
            pair!(ctx, pairs, unitvector(ctx, id))
            f5sat_core!(ctx, G, H, koszul_q, pairs, S, sat_tag = [:h], zd_tag = :p; kwargs...)
            empty!(pairs)
            delete_indices!(ctx, G, [id])
        end
    end
end

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
    sort!(pairs, lt = (p1, p2) -> Base.Order.lt(pairordering(ctx), p1, p2))
    G, H, koszul_queue(ctx), pairs
end
    
function core_loop!(ctx::SΓ,
                    G::Basis{I, M},
                    H::Syz{I, M},
                    koszul_q::KoszulQueue{I, M, SΓ},
                    pairs::PairSet{I, M},
                    select,
                    all_koszul,
                    curr_sort_id;
                    kwargs...) where {I, M, SΓ <: SigPolynomialΓ{I, M}}
    
    @logmsg Verbose2 "" start_time_core = time()
    @logmsg Verbose1 "" (curr_sort_id = sort_id(ctx, first(pairs)[1]),
                         curr_index_hash = first(pairs)[1][2][1],
                         sig_degree = degree(ctx, first(pairs)[1]),
                         tag = tag(ctx, first(pairs)[1]))...
    @logmsg Verbose1 "" sugar_deg = mod_order(ctx) in [:DPOT, :SCHREY] ? sugar_deg = schrey_degree(ctx, first(pairs)[1]) : sugar_deg = -1
    @debug string("pairset:\n", [isnull(p[2]) ? "$((p[1], ctx))\n" : "$((p[1], ctx)), $((p[2], ctx))\n" for p in pairs]...)

    to_reduce, sig_degree, are_pairs = select!(ctx, G, koszul_q, pairs, Val(select), all_koszul; kwargs...)
    if isempty(to_reduce)
        return f5_matrix(ctx, easytable(M[]), easytable(M[]), Tuple{MonSigPair{I, M}, eltype(ctx.po), eltype(ctx.mod_po)}[])
    end
    
    @logmsg Verbose2 "" indx = mod_order(ctx) == :POT && !(isempty(to_reduce)) ? maximum(p -> sort_id(ctx, p), to_reduce) : 0
    @logmsg Verbose2 "" min_deg = minimum(p -> degree(ctx.po, ctx(p...).pol), to_reduce)
    
    table, module_table, sigpolys = symbolic_pp!(ctx, to_reduce, G, H, all_koszul, curr_sort_id,
                                                 are_pairs = are_pairs; kwargs...)
    mat = f5_matrix(ctx, table, module_table, sigpolys)
    
    @logmsg Verbose2 "" nz_entries = sum([length(rw) for rw in mat.rows]) mat_size = (length(mat.rows), length(mat.tbl))
    
    reduction!(mat)
    return mat
end

function new_elems!(ctx::SΓ,
                    G::Basis{I, M},
                    H::Syz{I, M},
                    pairs::PairSet{I, M},
                    mat::F5matrix,
                    all_koszul,
                    curr_sort_id::I;
                    kwargs...) where {I, M, SΓ <: SigPolynomialΓ{I, M}}

    for (i, (sig, row)) in enumerate(zip(mat.sigs, mat.rows))
        @debug "considering $((sig, ctx))"
        if mod_order(ctx) == :POT
            if sort_id(ctx, sig) < curr_sort_id
                @debug "skipping $((sig, ctx))"
                continue
            end
        end
        new_sig = mul(ctx, sig...)
        if isempty(row)
            @debug "old leading monomial $(gpair(ctx.po.mo, leadingmonomial(ctx, sig..., no_rewrite = true)))"
            @debug "syzygy $((sig, ctx))"
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
            @debug "old leading monomial $(gpair(ctx.po.mo, leadingmonomial(ctx, sig..., no_rewrite = true)))"
            @debug "new leading monomial $(gpair(ctx.po.mo, lm))"
            @debug "is a unitvector to add: $((isunitvector(ctx, new_sig) && !(new_sig in G.sigs)))"
            @debug "leading monomial changed: $(lt(ctx.po.mo, lm, leadingmonomial(ctx, sig..., no_rewrite = true)))"
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
                new_basis_elem!(G, new_sig, lm)
                pairs!(ctx, pairs, new_sig, lm, G, H; kwargs...)
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
    @logmsg Verbose2 "" gb_size_aft_interred = gb_size(ctx, G.sigs)
end

function debug_sgb!(;io = stdout)
    no_fmt(args...) = :normal, "", ""
    logger = ConsoleLogger(io, Logging.LogLevel(-1000), meta_formatter = no_fmt)
    global_logger(logger)
    global_logger(logger)
end
