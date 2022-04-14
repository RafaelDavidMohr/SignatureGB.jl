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
include("./gen_example_file.jl")

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
    R = parent(first(I))
    G, H, koszul_q, pairs = pairs_and_basis(ctx, length(I))
    logger = SGBLogger(ctx, verbose = verbose; kwargs...)
    with_logger(logger) do
        sgb_core!(ctx, G, H, koszul_q, pairs, R; kwargs...)
        verbose == 2 && printout(logger)
    end
    [R(ctx, g[1]) for g in G]
end

function f5sat(I::Vector{P},
               to_sat::P;
               verbose = 0,
               kwargs...) where {P<:AA.MPolyElem}

    R = parent(first(I))
    ctx = setup(I; mod_rep_type = :highest_index,
                mod_order = :POT,
                track_module_tags = [:to_sat],
                kwargs...)
    new_generator!(ctx, length(I) + 1, ctx.po(to_sat), :to_sat)
    G, H, koszul_q, pairs = pairs_and_basis(ctx, length(I) + 1)
    logger = SGBLogger(ctx, verbose = verbose, task = :sat; kwargs...)
    with_logger(logger) do
        f5sat_core!(ctx, G, H, koszul_q, pairs, R; kwargs...)
        verbose == 2 && printout(logger)
    end
    [R(ctx, g[1]) for g in filter(g -> tag(ctx, g[1]) != :to_sat, G)]
end    

function f45sat(I::Vector{P},
                to_sat::P;
                verbose = 0,
                kwargs...) where {P<:AA.MPolyElem}

    R = parent(first(I))
    ctx = setup(I; mod_rep_type = :highest_index,
                mod_order = :DPOT,
                track_module_tags = [:to_sat],
                kwargs...)
    sat_indx_key = new_generator!(ctx, length(I) + 1, ctx.po(to_sat), :to_sat)
    G, H, koszul_q, pairs = pairs_and_basis(ctx, length(I))
    logger = SGBLogger(ctx, verbose = verbose, task = :f4sat; kwargs...)
    with_logger(logger) do
        f45sat_core!(ctx, G, H, koszul_q, pairs, R, sat_indx_key; kwargs...)
        verbose == 2 && printout(logger)
    end
    [R(ctx, g[1]) for g in G]
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
	nondegen_part_core!(ctx, G, H, koszul_q, remaining, R; kwargs...)
        verbose == 2 && printout(logger)
    end
    [R(ctx, g[1]) for g in G]
end

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

struct DecompResult{P}
    result::Vector{Tuple{Vector{P}, Int64, Symbol, Symbol}}
end

function Base.show(io::IO, res::DecompResult)
    for (comp, i, t, s) in res.result
        if s == :lower_dim
            if t == :lower_dim
                println(io, "component obtained on level $(i) of lower dimension coming from component of lower dimension")
            else
                println(io, "component obtained on level $(i) of lower dimension coming from nondegenerate part")
            end
        else
            println(io, "nondegenerate part")
        end
    end
end
    
function decomp(I::Vector{P};
                verbose = 0,
                kwargs...) where {P <: AA.MPolyElem}

    if length(I) > Singular.nvars(parent(first(I)))
        error("Put in a number of polynomials less than or equal to the number of variables")
    end
    ctx = setup([I[1]]; mod_rep_type = :highest_index,
                mod_order = :POT,
                track_module_tags = [:f, :zd],
                kwargs...)
    G, H, koszul_q, _ = pairs_and_basis(ctx, 1, start_gen = 2)
    remaining = [ctx.po(f) for f in I[2:end]]
    logger = SGBLogger(ctx, verbose = verbose, task = :decomp)
    with_logger(logger) do
	components = decomp_core!(ctx, G, H, koszul_q, remaining; kwargs...)
        verbose == 2 && printout(logger)
        R = parent(first(I))
        return DecompResult([([R(ctx, g[1]) for g in G], i, t, s) for (ctx, G, i, t, s) in components])
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
                   max_remasks = 3,
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
    
    if isnothing(select)
        if mod_order(ctx) == :POT
            select = :deg_and_pos
        elseif mod_order(ctx) == :SCHREY || mod_order(ctx) == :DPOT
            select = :schrey_deg
        end
    end

    if deg_bound > 0 && mod_order(ctx) != :DPOT
        error("only put deg_bound > 0 if you use :DPOT as a module order")
    end

    if f5c
        !(all_koszul) && error("Something is currently breaking when using f5c and not checking against all koszul syzygies. We are working hard to fix it :-)")
        mod_order(ctx) != :POT && error("F5c only makes sense for position over term ordering.")
    end

    # TEMP: temporary solution to not correctly symbolically preproc. the unit vectors
    select_both = mod_order(ctx) == :POT

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
        
        # TODO: is this a good idea?
        if max_remasks > 0 && rand() < max(1/max_remasks, 1/3)
            max_remasks -= 1
            remask!(ctx.po.mo.table)
        end
        to_reduce, done = core_loop!(ctx, G, H, koszul_q, pairs, select, all_koszul, f5c = f5c, select_both = select_both)
        @logmsg Verbose2 "" indx = mod_order(ctx) == :POT && !(isempty(to_reduce)) ? maximum(p -> index(ctx, p), to_reduce) : 0
        isempty(to_reduce) && continue
        mat = F5matrix(ctx, done, collect(to_reduce), f5c = f5c)
        @logmsg Verbose2 "" nz_entries = sum([length(rw) for rw in values(rows(mat))]) mat_size = (length(rows(mat)), length(tbl(mat)))
        reduction!(mat)
        
        met_syz = new_elems!(ctx, G, H, pairs, mat, all_koszul, f5c = f5c)
        @logmsg Verbose2 "" end_time_core = time()
        @logmsg Verbose2 "" gb_size = gb_size(ctx, G)
        if exit_upon_zero_reduction && met_syz
            return
        end
    end
end

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

function f5sat_core!(ctx::SΓ,
                     G::Basis{I,M},
                     H::Syz{I,M},
                     koszul_q::KoszulQueue{I,M,SΓ},
                     pairs::PairSet{I,M,SΓ},
                     R;
                     max_remasks = 3,
                     sat_tag = :to_sat,
                     f5c = false,
                     just_colon = false,
                     kwargs...) where {I,M,SΓ<:SigPolynomialΓ{I,M}}

    if !(extends_degree(termorder(ctx.po.mo)))
        error("I currently don't know how to deal with non-degree based monomial orderings...")
    end

    select = :deg_and_pos
    all_koszul = true
    curr_indx = index(ctx, first(pairs)[1])
    old_gb_length = length(G)
    
    while !(isempty(pairs))
        # TODO: is this a good idea
        if max_remasks > 0 && rand() < max(1 / max_remasks, 1 / 3)
            max_remasks -= 1
            remask!(ctx.po.mo.table)
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

        to_reduce, done = core_loop!(ctx, G, H, koszul_q, pairs, select, all_koszul, select_both = false, f5c = f5c)
        isempty(done) && continue
        mat = F5matrix(ctx, done, collect(to_reduce), f5c = f5c)
        reduction!(mat)
        rws = rows(mat)
        @logmsg Verbose2 "" nz_entries = sum([length(pol(mat, rw)) for rw in values(rws)]) mat_size = (length(rws), length(tbl(mat)))

        max_sig = last(collect(keys(rws)))
        curr_indx_key = max_sig[2][1]
        @logmsg Verbose2 "" indx = index(ctx, max_sig) tag = tag(ctx, max_sig)
        if tag(ctx, max_sig) == sat_tag && !(just_colon)
            zero_red = filter(kv -> iszero(pol(mat, kv[2])), rws)
            if isempty(zero_red)
                new_elems!(ctx, G, H, pairs, mat, all_koszul, f5c = f5c; kwargs...)
                @logmsg Verbose2 "" gb_size = gb_size(ctx, G)
            else
                # zero divisors to insert
                @debug string("inserting pols coming from signatures\n", ["$((s, ctx))\n" for s in keys(zero_red)]...)
                pols_to_insert = (sig -> unindexpolynomial(tbl(mat.module_matrix), module_pol(mat, sig))).(keys(zero_red))

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
            new_elems!(ctx, G, H, pairs, mat, all_koszul, f5c = f5c; kwargs...)
            @logmsg Verbose2 "" gb_size = gb_size(ctx, G)
        end
        @logmsg Verbose2 "" end_time_core = time()
    end

    if just_colon
        for h in H
            if tag(ctx, h) == sat_tag
                p = project(ctx, h)
                indx_key = new_generator!(ctx, curr_indx, p, :p)
                new_basis_elem!(ctx, G, unitvector(ctx, indx_key))
            end
        end
        filter!(g -> tag(ctx, g[1]) != sat_tag, G)
        f5c && interreduction!(ctx, G, R)
    end
end

function f45sat_core!(ctx::SΓ,
                      G::Basis{I,M},
                      H::Syz{I,M},
                      koszul_q::KoszulQueue{I,M,SΓ},
                      pairs::PairSet{I,M,SΓ},
                      R,
                      sat_indx_key;
                      max_remasks = 3,
                      kwargs...) where {I,M,SΓ<:SigPolynomialΓ{I,M}}

    gen_degree = indx_key -> degree(ctx.po, ctx(unitvector(ctx, indx_key)).pol)
    deg_bound = 1
    sat_degree = degree(ctx.po, ctx(unitvector(ctx, sat_indx_key)).pol)
    sat_pairset = pairset(ctx)
    while !(isempty(pairs))
        @logmsg Verbose2 "" add_row = true gb_or_sat = :gb
        sgb_core!(ctx, G, H, koszul_q, pairs, R, all_koszul = true, deg_bound = deg_bound)
        pair!(ctx, sat_pairset, unitvector(ctx, sat_indx_key))
        if isempty(pairs)
            deg_bound = 0
        end
        @logmsg Verbose2 "" add_row = true gb_or_sat = :sat
        sgb_core!(ctx, G, H, koszul_q, sat_pairset, R, all_koszul = true, deg_bound = deg_bound,
                  exit_upon_zero_reduction = true)
        empty!(sat_pairset)

        zero_divisors = [project(ctx, h) for h in H if h[1] == sat_indx_key]
        if !(isempty(zero_divisors))
            println("found zero divisors in degree $(degree(ctx.po, first(zero_divisors)))")
        end
        min_new_index = maxindex(ctx)
        for p in zero_divisors
            larger_deg_gen_info = filter(kv -> kv[2].tag != :to_sat && gen_degree(kv[1]) > degree(ctx.po, p),
                                         collect(ctx.f5_indices))
            if isempty(larger_deg_gen_info)
                p_index = index(ctx, sat_indx_key)
            else
                p_index = minimum(kv -> kv[2].index, larger_deg_gen_info)
            end
            new_key = new_generator!(ctx, p_index, p, :zd)
            if p_index < min_new_index
                min_new_index = p_index
            end
        end
        collected_pairset = collect(pairs)
        empty!(pairs)
        for indx_key in keys(ctx.f5_indices)
            if index(ctx, indx_key) >= min_new_index && tag(ctx, indx_key) != :to_sat
                pair!(ctx, pairs, unitvector(ctx, indx_key))
            else
                for p in collected_pairset
                    if p[1][2][1] == indx_key
                        push!(pairs, p)
                    end
                end
            end
        end
        filter!(g -> index(ctx, g[1]) < min_new_index, G)
        filter!(h -> h[1] != sat_indx_key, H)
        filter!(g -> g[1][1] != sat_indx_key, G)
        deg_bound += 1
    end
end

function nondegen_part_core!(ctx::SΓ,
                             G::Basis{I, M},
                             H::Syz{I, M},
                             koszul_q::KoszulQueue{I, M, SΓ},
                             remaining::Vector{P},
                             R;
                             max_remasks = 3,
                             f5c = false,
                             kwargs...) where {I, M, SΓ <: SigPolynomialΓ{I, M},
                                               P <: Polynomial{M}}

    ngens = length(ctx.f5_indices)
    cleaning_info = eltype(ctx)[]
    pairs = pairset(ctx)
    
    for (i, f) in enumerate(remaining)
        last_index = maxindex(ctx)
        indx_key = new_generator!(ctx, f)
        pair!(ctx, pairs, unitvector(ctx, indx_key))
        # last_index = maximum(g -> index(ctx, g[1]), G)
        f5sat_core!(ctx, G, H, koszul_q, pairs, R,
                    max_remasks = max_remasks - i, sat_tag = :f; f5c = f5c, kwargs...)
        empty!(pairs)
        f5c && interreduction!(ctx, G, R)
        
        curr_index = ctx.f5_indices[indx_key].index
        gs = [k for (k, v) in ctx.f5_indices
                  if v.tag == :zd && last_index < v.index < curr_index]
        for k in gs
            syz = filter(h -> index(ctx, h) == index(ctx, k), H)
            isempty(syz) && continue
            hs = [project(ctx, h) for h in syz]
            for h in hs
                println("new cleaner $(R(ctx.po, h))")
            end
            cleaner = random_lin_comb(ctx.po, [project(ctx, h) for h in syz])
            new_indx_key = new_generator!(ctx, curr_index + 1, cleaner, :h)
            push!(cleaning_info, unitvector(ctx, new_indx_key))
        end

        for (j, cleaner) in enumerate(cleaning_info)
            if index(ctx, cleaner) < curr_index + 1
                new_index!(ctx, cleaner[1], curr_index + j, :h)
            end
            pair!(ctx, pairs, cleaner)
            f5sat_core!(ctx, G, H, koszul_q, pairs, R,
                        max_remasks = max_remasks - i, sat_tag = :h; f5c = f5c, kwargs...)
            empty!(pairs)
            filter!(g -> tag(ctx, g[1]) != :h, G)
        end
        
        empty!(pairs)
    end
end

function decomp_core!(ctx::SΓ,
                      G::Basis{I, M},
                      H::Syz{I, M},
                      koszul_q::KoszulQueue{I, M, SΓ},
                      remaining::Vector{P},
                      max_remasks = 3,
                      kwargs...) where {I, M, SΓ <: SigPolynomialΓ{I, M},
                                        P <: Polynomial{M}}

    ngens = length(ctx.f5_indices)
    components = [(ctx, G, H, 1, :nondeg, :nondeg)]
    
    for (i, f) in enumerate(remaining)
        for (j, (ctx, G, H, l, t, s)) in enumerate(copy(components))
            @logmsg Verbose2 "" add_row = true defaults = [(:component, j), (:level, i)]
            indx_key = new_generator!(ctx, f)
            pairs = pairset(ctx)
            pair!(ctx, pairs, unitvector(ctx, indx_key))
            last_index = maximum(g -> index(ctx, g[1]), G)
            G_old = copy(G)
            basis_before = [ctx(g[1]).pol for g in G_old]
            f5sat_core!(ctx, G, H, koszul_q, pairs, max_remasks = max_remasks, sat_tag = :f; kwargs...)
            ctx.f5_indices[indx_key].tag = :f

            # construct components of higher dimension
            curr_index = ctx.f5_indices[indx_key].index
            new_components = empty(components)
            gs = [(k, ctx(unitvector(ctx, k)).pol) for (k, v) in ctx.f5_indices
                      if v.tag == :zd && last_index < v.index < curr_index]
            if any(g -> isunit(ctx.po, g[2]), gs)
                components[j] = (ctx, G_old, H, l, t, s)
                continue
            end
            for (j, (zd_index, g)) in enumerate(gs)
                new_comp_pols = copy(basis_before)
                for k in 1:j-1
                    push!(new_comp_pols, g)
                end
                for sig in H
                    if sig[1] == zd_index[1]
                        p = project(ctx, sig)
                        push!(new_comp_pols, p)
                    end
                end
                ctx_new = sigpolynomialctx(ctx.po.co, 0,
                                           polynomials = ctx.po,
                                           track_module_tags = [:f, :zd],
                                           mod_rep_type = :highest_index)
                G_new = new_basis(ctx_new)
                H_new = new_syz(ctx_new)
                for (l, p) in enumerate(new_comp_pols)
                    new_generator!(ctx_new, l, p, :f)
                    new_basis_elem!(ctx_new, G_new, unitvector(ctx_new, l))
                end
                push!(new_components, (ctx_new, G_new, H_new, i+1, s, :lower_dim))
            end
            components = vcat(components, new_components)
        end
    end
    return [(ctx, G, i, t, s) for (ctx, G, H, i, t, s) in components]
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
    @logmsg Verbose2 "" min_deg = minimum(p -> degree(ctx.po, ctx(p...).pol), to_reduce)
    done = symbolic_pp!(ctx, to_reduce, G, H, all_koszul,
                        are_pairs = are_pairs; kwargs...)
    return to_reduce, done
end

function new_elems!(ctx::SΓ,
                    G::Basis{I, M},
                    H::Syz{I, M},
                    pairs::PairSet{I, M, SΓ},
                    mat::MacaulayMatrix,
                    all_koszul;
                    kwargs...) where {I, M, SΓ <: SigPolynomialΓ{I, M}}

    met_syz = false
    rws = rows(mat)
    for (sig, row) in rws
        @debug "considering $((sig, ctx))"
        if mod_order(ctx) == :POT
            max_indx = maximum(p -> index(ctx, p), keys(rws))
            index(ctx, sig) < max_indx && continue
        end
        new_sig = mul(ctx, sig...)
        if isempty(pol(mat, row))
            met_syz = true
            @debug "old leading monomial $(gpair(ctx.po.mo, leadingmonomial(ctx, sig..., no_rewrite = true)))"
            @debug "syzygy $((sig, ctx))"
            @logmsg Verbose2 "" new_syz = true
            push!(H, new_sig)
            if mod_rep_type(ctx) != nothing
                q = unindexpolynomial(tbl(mat.module_matrix),
                                          tail(module_pol(mat, sig)))
                ctx(new_sig, zero(q), q)
            else
                ctx(new_sig, zero(eltype(ctx.po)))
            end
            new_rewriter!(ctx, pairs, new_sig)
        else
            p = unindexpolynomial(tbl(mat), pol(mat, row))
            lm = leadingmonomial(p)
            @debug "old leading monomial $(gpair(ctx.po.mo, leadingmonomial(ctx, sig..., no_rewrite = true)))"
            @debug "new leading monomial $(gpair(ctx.po.mo, lm))"
            if (isunitvector(ctx, new_sig) && !((new_sig, lm) in G)) || lt(ctx.po.mo, lm, leadingmonomial(ctx, sig..., no_rewrite = true))
                @debug "adding $((sig, ctx))"
                new_info = true
                @logmsg Verbose2 "" new_basis = true
                new_rewriter!(ctx, pairs, new_sig)
                if mod_rep_type(ctx) == nothing
                    q = zero(eltype(ctx.po))
                elseif mod_rep_type(ctx) == :highest_index
                    q = unindexpolynomial(tbl(mat.module_matrix), tail(module_pol(mat, sig)))
                else
                    q = unindexpolynomial(tbl(mat.module_matrix), module_pol(mat, sig))
                end
                ctx(new_sig, p, q)
                push!(G, (new_sig, lm))
                pairs!(ctx, pairs, new_sig, lm, G, H, all_koszul; kwargs...)
            end
        end
    end
    return met_syz
end

function interreduction!(ctx::SigPolynomialΓ{I, M},
                         G::Basis{I, M},
                         R) where {I, M}

    @logmsg Verbose1 "" interred = true
    basis = [R(ctx.po, ctx(g[1]).pol) for g in G]
    interred_basis = (g -> ctx.po(g)).(gens(std(Ideal(R, basis), complete_reduction = true)))
    G_new = new_basis(ctx)
    for ((sig, _), p) in zip(G, interred_basis)
        ctx(sig, p)
        push!(G_new, (sig, leadingmonomial(p)))
    end
    empty!(G)
    for g_new in G_new
        push!(G, g_new)
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
