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
             verbose = 0,
             kwargs...) where {P <: AA.MPolyElem}

    ctx = setup(I; kwargs...)
    G, H, koszul_q, pairs = pairs_and_basis(ctx, length(I))
    logger = SGBLogger(ctx, verbose = verbose)
    with_logger(logger) do
        sgb_core!(ctx, G, H, koszul_q, pairs; kwargs...)
        if verbose == 2
            show(logger.core_info, show_row_number = false)
            print("\n")
        end
    end
    R = parent(first(I))
    [R(ctx, g[1]) for g in G]
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
        @logmsg Verbose2 "" start_time_core = time()
        to_reduce, are_pairs = select!(ctx, koszul_q, pairs, Val(select))
        isempty(to_reduce) && continue
        done = symbolic_pp!(ctx, to_reduce, G, H, use_max_sig = use_max_sig,
                            are_pairs = are_pairs)
        koszul_syzygies = [koszul_syz(ctx, a[1], b[1]) for (a, b) in combinations(G, 2)]
        mat = F5matrix(ctx, done, collect(to_reduce))
        @logmsg Verbose2 "" nz_entries = sum([length(rw) for rw in values(rows(mat))]) mat_size = (length(rows(mat)), length(tbl(mat)))
        reduction!(mat)
        for k in koszul_syzygies
            for a in to_reduce
                divides(ctx, k, mul(ctx, a...)) && error("$((a, ctx)) is koszul!")
            end
        end

        @inbounds begin
            for (sig, row) in rows(mat)
                new_sig = mul(ctx, sig...)
                if isempty(row)
                    @logmsg Verbose2 "" new_syz = true
                    push!(H, new_sig)
                    new_rewriter!(ctx, pairs, new_sig)
                else
                    p = unindexpolynomial(tbl(mat), row)
                    lm = leadingmonomial(p)
                    if (isunitvector(ctx, new_sig) && !(new_sig in G)) || lt(ctx.po.mo, lm, leadingmonomial(ctx, sig..., no_rewrite = true))
                        @logmsg Verbose2 "" new_basis = true
                        new_rewriter!(ctx, pairs, new_sig)
                        ctx(new_sig, p)
                        push!(G, (new_sig, lm))
                        pairs!(ctx, pairs, new_sig, lm, G, H)
                    end
                end
            end
        end
        @logmsg Verbose2 "" end_time_core = time()
    end
end

end
