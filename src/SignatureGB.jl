module SignatureGB
using Combinatorics

include("./useful.jl")
include("./context.jl")
include("./termorder.jl")
include("./polynomials.jl")
include("./coefficients.jl")
include("./monomialtable.jl")
include("./sigtable.jl")
include("./logging.jl")
include("./pairs.jl")
include("./symbolicpp.jl")
include("./reduction_better.jl")
# include("./interreduction.jl")
# include("./gen_example_file.jl")

export sgb, f5sat, nondegen_part, decomp

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
    G, H, koszul_q, pairs = pairs_and_basis(ctx, length(I))
    logger = SGBLogger(ctx, verbose = verbose)
    with_logger(logger) do
        sgb_core!(ctx, G, H, koszul_q, pairs; kwargs...)
        verbose == 2 && printout(logger)
    end
    R = parent(first(I))
    [R(ctx, g[1]) for g in G]
end

function f5sat(I::Vector{P},
    to_sat::P;
    verbose = 0,
    kwargs...) where {P<:AA.MPolyElem}

    ctx = setup(I; mod_rep_type = :highest_index,
        mod_order = :POT,
        track_module_tags = [:to_sat],
        kwargs...)
    new_generator!(ctx, length(I) + 1, to_sat, :to_sat)
    G, H, koszul_q, pairs = pairs_and_basis(ctx, length(I) + 1)
    logger = SGBLogger(ctx, verbose = verbose)
    with_logger(logger) do
        f5sat_core!(ctx, G, H, koszul_q, pairs; kwargs...)
        verbose == 2 && printout(logger)
    end
    R = parent(first(I))
    [R(ctx, g[1]) for g in filter(g -> tag(ctx, g[1]) != :to_sat, G)]
end    

function nondegen_part(I::Vector{P};
                       verbose = 0,
                       kwargs...) where {P <: AA.MPolyElem}

    if length(I) > Singular.nvars(parent(first(I)))
        error("Put in a number of polynomials less than or equal to the number of variables")
    end
    ctx = setup(I; mod_rep_type = :highest_index,
                mod_order = :POT,
                track_module_tags = [:to_sat],
                kwargs...)
    G, H, koszul_q, pairs = pairs_and_basis(ctx, 1, start_gen = 2)
    logger = SGBLogger(ctx, verbose = verbose)
    with_logger(logger) do
	nondegen_part_core!(ctx, G, H, koszul_q, pairs; kwargs...)
        verbose == 2 && printout(logger)
    end
    R = parent(first(I))
    [R(ctx, g[1]) for g in G]
end

function decomp(I::Vector{P};
                verbose = 0,
                kwargs...) where {P <: AA.MPolyElem}

    if length(I) > Singular.nvars(parent(first(I)))
        error("Put in a number of polynomials less than or equal to the number of variables")
    end
    ctx = setup(I; mod_rep_type = :highest_index,
                mod_order = :POT,
                track_module_tags = [:to_sat, :zd],
                kwargs...)
    G, H, koszul_q, _ = pairs_and_basis(ctx, 1, start_gen = 2)
    for i in 2:length(I)
        ctx.f5_indices[i].tag = :to_sat
    end
    logger = SGBLogger(ctx, verbose = verbose)
    with_logger(logger) do
	components = decomp_core!(ctx, G, H, koszul_q; kwargs...)
        verbose == 2 && printout(logger)
        R = parent(first(I))
        return [[R(ctx, g[1]) for g in G] for (ctx, G) in components]
    end
end

function sgb_core!(ctx::SΓ,
                   G::Basis{I, M},
                   H::Syz{I, M},
                   koszul_q::KoszulQueue{I, M, SΓ},
                   pairs::PairSet{I, M, SΓ};
                   select = nothing,
                   all_koszul = false,
                   max_remasks = 3,
                   kwargs...) where {I, M, SΓ <: SigPolynomialΓ{I, M}}

    if !(extends_degree(termorder(ctx.po.mo)))
        error("I currently don't know how to deal with non-degree based monomial orderings...")
    end

    if all_koszul
        if mod_order(ctx) != :POT
            error("checking against all Koszul syzygies currently only supported for position over term.")
        end
    end
    
    if isnothing(select)
        if mod_order(ctx) == :POT
            select = :deg_and_pos
        elseif mod_order(ctx) == :SCHREY
            select = :deg
        end
    end
        
    while !(isempty(pairs))
        # TODO: is this a good idea?
        if max_remasks > 0 && rand() < max(1/max_remasks, 1/3)
            max_remasks -= 1
            remask!(ctx.po.mo.table)
        end
        to_reduce, done = core_loop!(ctx, G, H, koszul_q, pairs, select, all_koszul)
        isempty(to_reduce) && continue
        mat = F5matrix(ctx, done, collect(to_reduce))
        @logmsg Verbose2 "" nz_entries = sum([length(rw) for rw in values(rows(mat))]) mat_size = (length(rows(mat)), length(tbl(mat)))
        reduction!(mat)
        
        new_elems!(ctx, G, H, pairs, mat, all_koszul)
        @logmsg Verbose2 "" end_time_core = time()
    end
end

function f5sat_core!(ctx::SΓ,
                     G::Basis{I, M},
                     H::Syz{I, M},
                     koszul_q::KoszulQueue{I, M, SΓ},
                     pairs::PairSet{I, M, SΓ};
                     max_remasks = 3,
                     kwargs...) where {I, M, SΓ <: SigPolynomialΓ{I, M}}

    if !(extends_degree(termorder(ctx.po.mo)))
        error("I currently don't know how to deal with non-degree based monomial orderings...")
    end
    
    select = :deg_and_pos
    all_koszul = true
    curr_indx = index(ctx, first(pairs)[1])
    
    while !(isempty(pairs))
        # TODO: is this a good idea
        if max_remasks > 0 && rand() < max(1/max_remasks, 1/3)
            max_remasks -= 1
            remask!(ctx.po.mo.table)
        end
        
        next_index = index(ctx, first(pairs)[1])
        if next_index != curr_indx
            curr_indx = next_index
        end
        
        to_reduce, done = core_loop!(ctx, G, H, koszul_q, pairs, select, all_koszul, select_both = false)
        isempty(done) && continue
        mat = F5matrixHighestIndex(ctx, done, collect(to_reduce))
        reduction!(mat)
        rws = rows(mat)
        @logmsg Verbose2 "" nz_entries = sum([length(pol(mat, rw)) for rw in values(rws)]) mat_size = (length(rws), length(tbl(mat)))
        
        max_sig = last(collect(keys(rws)))
        curr_indx_key = max_sig[2][1]
        @logmsg Verbose2 "" indx = index(ctx, max_sig) tag = tag(ctx, max_sig)
        if tag(ctx, max_sig) == :to_sat
            zero_red = filter(kv -> iszero(pol(mat, kv[2])), rws)
            if isempty(zero_red)
                new_elems!(ctx, G, H, pairs, mat, all_koszul)
            else
                # zero divisors to insert
                @debug string("inserting pols coming from signatures\n", ["$((s, ctx))\n" for s in keys(zero_red)]...)
                pols_to_insert = [unindexpolynomial(tbl(mat.module_matrix),
                                                    module_pol(mat, sig))
                                  for sig in keys(zero_red)]
                
                # cache some reduction results for future use
                for g in G
                    index(ctx, g[1]) == curr_indx && push!(ctx.cashed_sigs, g[1])
                end
                for (sig, row) in rws
                    isempty(pol(mat, row)) && continue
                    p = unindexpolynomial(tbl(mat), pol(mat, row))
                    lm = leadingmonomial(p)
                    if index(ctx, sig) == curr_indx && lt(ctx.po.mo, lm, leadingmonomial(ctx, sig..., no_rewrite = true))
                        @logmsg Verbose2 "" new_basis = true
                        q = unindexpolynomial(tbl(mat.module_matrix),
                                          tail(module_pol(mat, sig)))
                        ctx(mul(ctx, sig...), p, q)
                        push!(ctx.cashed_sigs, mul(ctx, sig...))
                    end
                end

                # insert the zero divisors
                for p in pols_to_insert
                    @logmsg Verbose2 "" new_syz = true
                    new_index_key = new_generator!(ctx, curr_indx, p, :zd)
                    # TODO: make this a function
                    if isunit(ctx.po, p)
                        new_basis_elem!(G, unitvector(ctx, new_index_key), one(ctx.po.mo))
                        return
                    end
                end
                # syz_signatures = [g[2] for g in filter(g -> g[1] == curr_index_key, G)]

                # rebuild pairset
                pairs = pairset(ctx)
                filter!(g -> index(ctx, g[1]) < curr_indx, G)
                pair!(ctx, pairs, unitvector(ctx, curr_indx_key))
                for index_key in keys(ctx.f5_indices)
                    sig = unitvector(ctx, index_key)
                    if index(ctx, sig) >= curr_indx && tag(ctx, sig) == :zd
                        pair!(ctx, pairs, sig)
                    end
                end
            end
        else
            new_elems!(ctx, G, H, pairs, mat, all_koszul)
        end
        @logmsg Verbose2 "" end_time_core = time()
    end
end

function nondegen_part_core!(ctx::SΓ,
                             G::Basis{I, M},
                             H::Syz{I, M},
                             koszul_q::KoszulQueue{I, M, SΓ},
                             pairs::PairSet{I, M, SΓ};
                             max_remasks = 3,
                             kwargs...) where {I, M, SΓ <: SigPolynomialΓ{I, M}}

    ngens = length(ctx.f5_indices)
    
    for i in 2:ngens
        ctx.f5_indices[i].tag = :to_sat
        pair!(ctx, pairs, unitvector(ctx, i))
        f5sat_core!(ctx, G, H, koszul_q, pairs, max_remasks = max_remasks; kwargs...)
        pairs = pairset(ctx)
    end
end

function decomp_core!(ctx::SΓ,
                      G::Basis{I, M},
                      H::Syz{I, M},
                      koszul_q::KoszulQueue{I, M, SΓ},
                      max_remasks = 3,
                      kwargs...) where {I, M, SΓ <: SigPolynomialΓ{I, M}}

    ngens = length(ctx.f5_indices)
    components = [(ctx, G, H)]
    
    for i in 2:ngens
        for (ctx, G, H) in copy(components)
            pairs = pairset(ctx)
            remaining = [k for (k, v) in ctx.f5_indices if v.tag == :to_sat]
            pair!(ctx, pairs, unitvector(ctx, remaining[1]))
            last_index = maximum(g -> index(ctx, g[1]), G)
            f5sat_core!(ctx, G, H, koszul_q, pairs, max_remasks = max_remasks; kwargs...)
            ctx.f5_indices[remaining[1]].tag = :f

            # construct components of higher dimension
            curr_index = ctx.f5_indices[i].index
            G_new = filter(g -> index(ctx, g[1]) < curr_index && tag(ctx, g[1]) != :zd, G)
            gs = collect(filter(kv -> kv[2].tag == :zd && last_index < kv[2].index < curr_index, ctx.f5_indices))
            for (j, zd_index) in enumerate(gs)
                new_comp_pols = [ctx(g[1]).pol for g in G_new]
                non_triv = false
                for k in 1:j-1
                    non_triv = true
                    push!(new_comp_pols, ctx(unitvector(ctx, gs[k][1])).pol)
                end
                for sig in H
                    if sig[1] == zd_index[1]
                        non_triv = true
                        push!(new_comp_pols, project(ctx, sig))
                    end
                end
                !(non_triv) && continue
                ctx_new = sigpolynomialctx(ctx.po.co, 0,
                                           polynomials = ctx.po,
                                           track_module_tags = [:to_sat, :zd],
                                           mod_rep_type = :highest_index)
                G_new = new_basis(ctx_new)
                H_new = new_syz(ctx_new)
                for (l, p) in enumerate(new_comp_pols)
                    new_generator!(ctx_new, l, p, :f)
                    new_basis_elem!(ctx_new, G_new, unitvector(ctx_new, l))
                end
                if i < ngens
                    next_eqn = ctx(unitvector(ctx, i + 1)).pol
                    new_generator!(ctx_new, length(new_comp_pols) + 1, next_eqn, :to_sat)
                end
                push!(components, (ctx_new, G_new, H_new))
            end
        end
    end
    return [(ctx, G) for (ctx, G, H) in components]
end

function core_loop!(ctx::SΓ,
                    G::Basis{I, M},
                    H::Syz{I, M},
                    koszul_q::KoszulQueue{I, M, SΓ},
                    pairs::PairSet{I, M, SΓ},
                    select,
                    all_koszul;
                    kwargs...) where {I, M, SΓ <: SigPolynomialΓ{I, M}}
    
    @logmsg Verbose2 "" start_time_core = time()
    @logmsg Verbose1 "" curr_index = index(ctx, first(pairs)[1]) sig_degree = degree(ctx, first(pairs)[1]) tag = tag(ctx, first(pairs)[1])
    @debug string("pairset:\n", [isnull(p[2]) ? "$((p[1], ctx))\n" : "$((p[1], ctx)), $((p[2], ctx))\n" for p in pairs]...)
    to_reduce, sig_degree, are_pairs = select!(ctx, koszul_q, pairs, Val(select), all_koszul; kwargs...)
    if isempty(to_reduce)
        return to_reduce, M[]
    end
    done = symbolic_pp!(ctx, to_reduce, G, H, all_koszul,
                        are_pairs = are_pairs)
    return to_reduce, done
end

function new_elems!(ctx::SΓ,
                    G::Basis{I, M},
                    H::Syz{I, M},
                    pairs::PairSet{I, M, SΓ},
                    mat::MacaulayMatrix,
                    all_koszul) where {I, M, SΓ <: SigPolynomialΓ{I, M}}

    rws = rows(mat)
    for (sig, row) in rws
        new_sig = mul(ctx, sig...)
        @debug "considering $((sig, ctx))"
        if isempty(pol(mat, row))
            @debug "syzygy $((sig, ctx))"
            @logmsg Verbose2 "" new_syz = true
            push!(H, new_sig)
            if mod_rep_type(ctx) != nothing
                q = unindexpolynomial(tbl(mat.module_matrix),
                                          tail(module_pol(mat, sig)))
                ctx(new_sig, zero(q), q)
            end
            new_rewriter!(ctx, pairs, new_sig)
        else
            p = unindexpolynomial(tbl(mat), pol(mat, row))
            lm = leadingmonomial(p)
            # @debug "old leading monomial $(gpair(ctx.po.mo, leadingmonomial(ctx, sig..., no_rewrite = true)))"
            # @debug "new leading monomial $(gpair(ctx.po.mo, lm))"
            if (isunitvector(ctx, new_sig) && !((new_sig, lm) in G)) || lt(ctx.po.mo, lm, leadingmonomial(ctx, sig..., no_rewrite = true))
                @debug "adding $((sig, ctx))"
                new_info = true
                @logmsg Verbose2 "" new_basis = true
                new_rewriter!(ctx, pairs, new_sig)
                if mod_rep_type(ctx) != nothing
                    q = unindexpolynomial(tbl(mat.module_matrix),
                                          tail(module_pol(mat, sig)))
                    ctx(new_sig, p, q)
                else
                    ctx(new_sig, p)
                end
                push!(G, (new_sig, lm))
                pairs!(ctx, pairs, new_sig, lm, G, H, all_koszul)
            end
        end
    end
end

function debug_sgb!(;io = stdout)
    no_fmt(args...) = :normal, "", ""
    logger = ConsoleLogger(io, Logging.LogLevel(-1000), meta_formatter = no_fmt)
    global_logger(logger)
    global_logger(logger)
end

end
