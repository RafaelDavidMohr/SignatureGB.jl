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
# include("./f5data.jl")
include("./pairs.jl")
include("./symbolicpp.jl")
include("./reduction_better.jl")
# include("./interreduction.jl")
# include("./gen_example_file.jl")

export sgb, f5sat

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

function sgb(I::Vector{P};
             verbose = 0,
             kwargs...) where {P <: AA.MPolyElem}

    ctx = setup(I; kwargs...)
    G, H, koszul_q, pairs = pairs_and_basis(ctx, length(I))
    logger = SGBLogger(ctx, verbose = verbose)
    with_logger(logger) do
        sgb_core!(ctx, G, H, koszul_q, pairs; kwargs...)
        if verbose == 2
            show(logger.core_info, show_row_number = false, allrows = true)
            print("\n")
        end
    end
    R = parent(first(I))
    [R(ctx, g[1]) for g in G]
end

function f5sat(I::Vector{P},
               to_sat::P;
               verbose = 0,
               kwargs...) where {P <: AA.MPolyElem}

    ctx = setup(I; mod_rep_type = :highest_index,
                mod_order = :POT,
                track_module_tags = [:to_sat],
                kwargs...)
    new_generator!(ctx, pos_type(ctx)(length(I) + 1), to_sat, :to_sat)
    G, H, koszul_q, pairs = pairs_and_basis(ctx, length(I) + 1)
    logger = SGBLogger(ctx, verbose = verbose)
    with_logger(logger) do
	f5sat_core!(ctx, G, H, koszul_q, pairs)
        if verbose == 2
            show(logger.core_info, show_row_number = false, allrows = true)
            print("\n")
        end
    end
    R = parent(first(I))
    [R(ctx, g[1]) for g in filter(g -> tag(ctx, g[1]) != :to_sat, G)]
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
    else
        use_max_sig = true
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
        # TODO: is this a good idea
        if max_remasks > 0 && rand() < max(1/max_remasks, 1/3)
            max_remasks -= 1
            remask!(ctx.po.mo.table)
        end
        to_reduce, done = core_loop!(ctx, G, H, koszul_q, pairs, select, all_koszul, use_max_sig)
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
    else
        use_max_sig = true
    end
    
    select = :deg_and_pos
    all_koszul = true
    curr_tag = tag(ctx, first(pairs)[1])
    
    while !(isempty(pairs))
        # TODO: is this a good idea
        if max_remasks > 0 && rand() < max(1/max_remasks, 1/3)
            max_remasks -= 1
            remask!(ctx.po.mo.table)
        end
        
        next_tag = tag(ctx, first(pairs)[1])
        if curr_tag == :to_sat && next_tag != :to_sat
            filter(g -> tag(ctx, g[1]) != :to_sat, G)
        end
        curr_tag = next_tag
        
        to_reduce, done = core_loop!(ctx, G, H, koszul_q, pairs, select, all_koszul, use_max_sig)
        isempty(done) && continue
        mat = F5matrixHighestIndex(ctx, done, collect(to_reduce))
        reduction!(mat)
        rws = rows(mat)
        @logmsg Verbose2 "" nz_entries = sum([length(pol(mat, rw)) for rw in values(rws)]) mat_size = (length(rws), length(tbl(mat)))
        
        max_sig = last(collect(keys(rws)))
        @logmsg Verbose2 "" indx = index(ctx, max_sig) tag = tag(ctx, max_sig)
        if tag(ctx, max_sig) == :to_sat
            zero_red = filter(kv -> iszero(pol(mat, kv[2])), rws)
            if isempty(zero_red)
                new_elems!(ctx, G, H, pairs, mat, all_koszul)
            else
                pols_to_insert = [unindexpolynomial(tbl(mat.module_matrix),
                                                    module_pol(mat, sig))
                                  for sig in keys(zero_red)]
                curr_index_key = max_sig[2][1]
                curr_index = index(ctx, max_sig)
                for p in pols_to_insert
                    new_generator!(ctx, curr_index, p, :zd)
                end
                # syz_signatures = [g[2] for g in filter(g -> g[1] == curr_index_key, G)]
                pairs = pairset(ctx)
                filter!(g -> index(ctx, g[1]) < curr_index, G)
                for index_key in keys(ctx.f5_indices)
                    sig = unitvector(ctx, index_key)
                    if index(ctx, sig) >= curr_index
                        pair!(ctx, pairs, sig)
                    end
                end
            end
        else
            new_elems!(ctx, G, H, pairs, mat, all_koszul)
        end
    end
end
    
    
function core_loop!(ctx::SΓ,
                    G::Basis{I, M},
                    H::Syz{I, M},
                    koszul_q::KoszulQueue{I, M, SΓ},
                    pairs::PairSet{I, M, SΓ},
                    select,
                    all_koszul,
                    use_max_sig) where {I, M, SΓ <: SigPolynomialΓ{I, M}}
    
    @logmsg Verbose2 "" start_time_core = time()
    @logmsg Verbose1 "" curr_index = index(ctx, first(pairs)[1]) sig_degree = degree(ctx, first(pairs)[1])
    to_reduce, sig_degree, are_pairs = select!(ctx, koszul_q, pairs, Val(select), all_koszul)
    isempty(to_reduce) && return to_reduce, M[]
    done = symbolic_pp!(ctx, to_reduce, G, H, all_koszul, use_max_sig = use_max_sig,
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
        if isempty(pol(mat, row))
            @logmsg Verbose2 "" new_syz = true
            push!(H, new_sig)
            new_rewriter!(ctx, pairs, new_sig)
        else
            p = unindexpolynomial(tbl(mat), pol(mat, row))
            lm = leadingmonomial(p)
            if (isunitvector(ctx, new_sig) && !((new_sig, lm) in G)) || lt(ctx.po.mo, lm, leadingmonomial(ctx, sig..., no_rewrite = true))
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
end
