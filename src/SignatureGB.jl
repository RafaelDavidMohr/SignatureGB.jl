module SignatureGB

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

# converting a vector of singular polynomials into our own data structures
function f5setup(I::Vector{P};
                 mod_order=:POT,
                 mon_order=:GREVLEX,
                 index_type=UInt32,
                 mask_type=UInt32,
                 pos_type=UInt32,
                 trace_sig_tails = false,
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
    dat = f5data(I, mod_order = mod_order, trace_sig_tails = trace_sig_tails,
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
                 verbose = false) where {I, M, SΓ <: SigPolynomialΓ{I, M}}
    
    ctx = dat.ctx
    R = dat.R
    use_max_sig = (select == :deg_and_pos || select == :pos)
    orig_length = length(ctx.ord_indices)
    
    cnt = 1
    num_arit_operations_groebner = 0
    num_arit_operations_module_overhead = 0
    num_arit_operations_interreduction = 0
    curr_pos = zero(pos_type(ctx))

    while !(isempty(pairs))
        #- INTERREDUCTION -#
        indx = pos(ctx, first(pairs)[1])
        if indx != curr_pos && mod_order(dat.ctx) == :POT
            verbose && println("-----------")
            if dat.remasks_left > 0
                remask!(dat.ctx.po.mo.table)
                dat.remasks_left -= 1
            end
            @debug begin
                println("before interreduction")
                gb = [R(dat.ctx, (i, g[1])) for i in keys(G) for g in G[i]]
                !(is_gb(gb)) && error("not a groebner basis")
            end
            if interreduction && indx > 2
                verbose && println("INTERREDUCING")
                G, arit_ops = interreduce(ctx, G, H, verbose = verbose)
                num_arit_operations_interreduction += arit_ops
                @debug begin
                    println("after interreduction")
                    gb = [R(dat.ctx, (i, g[1])) for i in keys(G) for g in G[i]]
                    !(is_gb(gb)) && error("not a groebner basis")
                end
            end
            if verbose
                if first(pairs)[1][2][1] <= orig_length
                    println("STARTING WITH INDEX $(indx) (ORIGINAL ELEMENT)")
                else
                    println("STARTING WITH INDEX $(indx)")
                end
                println("-----------")
            end
            curr_pos = indx
        end
        
        
        #- PAIR SELECTION -#
        total_num_pairs = length(pairs)
        to_reduce, are_pairs, nselected, indx, max_key, tagg, sig_degree = select!(ctx, pairs, Val(select), select_both = select_both)

        #- SYMBOLIC PP -#
        symbolic_pp_timed  = @timed symbolic_pp!(ctx, to_reduce, G, H,
                                                 use_max_sig = use_max_sig,
                                                 sig_degree = sig_degree,
                                                 max_sig_pos = curr_pos,
                                                 are_pairs = are_pairs,
                                                 enable_lower_pos_rewrite = !(interreduction))
        done = symbolic_pp_timed.value
        symbolic_pp_time = symbolic_pp_timed.time
        mat = f5matrix(ctx, done, collect(to_reduce), indx, max_key, tagg,
                       enable_lower_pos_rewrite = !(interreduction))
        mat_size = (length(rows(mat)), length(mat.tbl))
        mat_dens = sum([length(rw) for rw in rows(mat)]) / (mat_size[1] * mat_size[2])

        #- REDUCTION -#
        reduction_dat = @timed reduction!(mat, trace_sig_tails = dat.trace_sig_tails)
        num_arit_operations_groebner += reduction_dat.value[1]
        num_arit_operations_module_overhead += reduction_dat.value[2]

        #- PAIR GENERATION -#
        pair_gen_dat = @timed new_elems(ctx, mat, pairs, G, H,
                                        enable_lower_pos_rewrite = !(interreduction))
        pairs = pair_gen_dat.value
        pair_gen_time = pair_gen_dat.time

        #- PRINTING INFORMATION -#
        if verbose
            zero_red_count = 0
            println("selected $(nselected) / $(total_num_pairs) pairs, sig-degree of sel. pairs: $(sig_degree)")
            println("symbolic pp took $(symbolic_pp_time) seconds.")
            println("Matrix $(cnt) : $(reduction_dat.time) secs reduction / size = $(mat_size) / density = $(mat_dens)")
            for (sig, rw) in mat.sigs_rows
                if isempty(rw)
                    zero_red_count += 1
                end
            end
            if !(iszero(zero_red_count))
                println("$(zero_red_count) zero reductions at sig-degree $(sig_degree) / position $(curr_pos)")
            end
            println("Pair generation took $(pair_gen_time) seconds.")
        end
        
        cnt += 1
    end

    verbose && println("-----")
    
    if interreduction
        verbose && println("FINAL INTERREDUCTION STEP")
        G, arit_ops = interreduce(ctx, G, H, verbose = verbose)
        num_arit_operations_interreduction += arit_ops
        verbose && println("-----")
    end

    if verbose
        println("total number of arithmetic operations (groebner): $(num_arit_operations_groebner)")
        println("total number of arithmetic operations (module overhead): $(num_arit_operations_module_overhead)")
        println("total number of arithmetic operations (interreduction): $(num_arit_operations_interreduction)")
    end
    G
end

function f5(I::Vector{P};
            start_gen = 1,
            trace_sig_tails = false,
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
                  trace_sig_tails = trace_sig_tails,
                  max_remasks = max_remasks, kwargs...)
    G, H, pairs = pairs_and_basis(dat, length(I), start_gen = start_gen)
    G = f5core!(dat, G, H, pairs, select = select, interreduction = interreduction, verbose = verbose)
    [R(dat.ctx, (i, g[1])) for i in keys(G) for g in G[i]]
end

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
                  trace_sig_tails = true,
                  max_remasks = max_remasks, kwargs...)
    G, H, pairs = pairs_and_basis(dat, length(I), start_gen = start_gen)
    G = f5core!(dat, G, H, pairs, select = select, verbose = verbose,
                new_elems = new_elems_decomp!, select_both = false,
                interreduction = interreduction)
    [R(dat.ctx, (i, g[1])) for i in keys(G) for g in G[i]]
end

function saturate(dat::F5Data{I, SΓ},
                  G::Basis{I, M},
                  H::Syz{I, M},
                  pol::Polynomial{M, T};
                  verbose = false) where {I, M, T, SΓ <: SigPolynomialΓ{I, M, T}}

    ctx = dat.ctx
    max_pos = maximum(i -> ctx.ord_indices[i][:position], keys(G))
    new_pos_key = maximum(keys(ctx.ord_indices)) + one(I)
    new_gen!(ctx, max_pos + one(I), :f, pol)
    
    pairs = pairset(ctx)
    new_sig = (new_pos_key, one(ctx.po.mo))
    G[new_pos_key] = Tuple{M, M}[]
    H[new_pos_key] = M[]
    pair!(ctx, pairs, new_sig)

    G = f5core!(dat, G, H, pairs, verbose = verbose,
                new_elems = new_elems_decomp!, select_both = false)
    filter!(kv -> kv[1] != new_pos_key, G)
    filter!(kv -> kv[1] != new_pos_key, H)
    G, H
end
end
