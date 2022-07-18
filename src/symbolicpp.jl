function find_reducer(ctx::SigPolynomialΓ{I, M},
                      G::Basis{I, M},
                      H::Syz{I, M},
                      m::M,
                      all_koszul,
                      curr_sort_id,
                      compatibility_check_id::I,
                      sig_degree::E;
                      # interreduction_step = false,
                      f5c = false,
                      kwargs...) where {I, M, E}

    if mod_order(ctx) == :SCHREY
        cond = p -> schrey_degree(ctx, p) <= sig_degree
    elseif mod_order(ctx) == :DPOT
        cond = p -> sort_id(ctx, p) <= curr_sort_id
    elseif mod_order(ctx) == :POT
        cond = p -> sort_id(ctx, p) < curr_sort_id || degree(ctx, p) <= sig_degree
    else
        cond = p -> degree(ctx, p) <= sig_degree
    end

    reducer = nullmonsigpair(ctx)
    mpairord = mpairordering(ctx)
    for (j, lm) in enumerate(G.lms)
        if divides(ctx.po.mo, lm, m)
            !(are_compatible(ctx, compatibility_check_id, G.sigs[j][1])) && continue
            delta = div(ctx.po.mo, m, lm)
            g = G.sigs[j]
            !(cond((delta, g))) && continue
            if !(f5c) || sort_id(ctx, g) == curr_sort_id
                rewriteable(ctx, delta, g, j, G, H, all_koszul) && continue
            end
            if isnull(reducer) || Base.Order.lt(mpairord, (delta, g), reducer)
                reducer = (delta, g)
                f5c && sort_id(ctx, g) < curr_sort_id && break
            end
        end
    end    
    return reducer
end

function symbolic_pp!(ctx::SΓ,
                      pairs::MS,
                      G::Basis{I, M},
                      H::Syz{I, M},
                      all_koszul,
                      curr_sort_id;
                      are_pairs = true,
                      f5c = false,
                      kwargs...) where {I, M,
                                        MS <: Union{MonSigSet{I, M}, Set{MonSigPair{I, M}}},
                                        SΓ <: SigPolynomialΓ{I, M}}

    # TODO: get this to work without the (now missing) index function
    @debug "symbolic preprocessing..."
    get_orig_elem = p -> f5c && sort_id(ctx, p) < curr_sort_id
    if mod_order(ctx) == :SCHREY || mod_order(ctx) == :DPOT
        sig_degree = maximum(p -> schrey_degree(ctx, p), pairs)
    elseif mod_order(ctx) == :POT
        sig_degree = maximum(p -> degree(ctx, p), filter(p -> sort_id(ctx, p) == curr_sort_id, pairs))
    else
        sig_degree = maximum(p -> degree(ctx, p), pairs)
    end

    compatibility_check_id = first(pairs)[2][1]
    
    # TODO: make this work without monomial table
    tbl = easytable(M[], eltype(ctx.po.mo))
    module_tbl = easytable(eltype(ctx.mod_po.mo)[], eltype(ctx.po.mo))
    sigpolys = Tuple{MonSigPair{I, M}, eltype(ctx.po), eltype(ctx.mod_po)}[]
    sizehint!(sigpolys, length(pairs))
    done = Set{M}()
    are_pairs && sizehint!(done, length(pairs) >> 1)
    for (i, p) in enumerate(pairs)
        pol = ctx(p..., no_rewrite = get_orig_elem(p)).pol
        if mod_rep_type(ctx) == :highest_index && tag(ctx, p) in ctx.track_module_tags && sort_id(ctx, p) == curr_sort_id
            module_pol = project(ctx, p..., no_rewrite = get_orig_elem(p))
            @debug "reading module rep $(gpair(ctx.po, module_pol)) for sig $((p, ctx))"
        else
            module_pol = zero(eltype(ctx.mod_po))
        end
        are_pairs && iseven(i) && push!(done, leadingmonomial(pol))
        for m in pol.mo
            findorpush!(tbl, m)
        end
        for m in module_pol.mo
            findorpush!(module_tbl, m)
        end
        push!(sigpolys, (p, pol, module_pol))
    end
        
    for m in tbl.val
        m in done && continue
        red = find_reducer(ctx, G, H, m, all_koszul, curr_sort_id,
                           compatibility_check_id, sig_degree,
                           f5c = f5c;
                           kwargs...)
        isnull(red) && continue
        @debug "found reducer $((red, ctx)) for $(gpair(ctx.po.mo, m))"
        pol = ctx(red..., no_rewrite = get_orig_elem(red)).pol
        if mod_rep_type(ctx) == :highest_index && tag(ctx, red) in ctx.track_module_tags && sort_id(ctx, red) == curr_sort_id
            module_pol = project(ctx, red..., no_rewrite = get_orig_elem(red))
            @debug "reading module rep $(gpair(ctx.po, module_pol)) for sig $((red, ctx))"
        else
            module_pol = zero(eltype(ctx.mod_po))
        end
        for m in pol.mo
            findorpush!(tbl, m)
        end
        for m in module_pol.mo
            findorpush!(module_tbl, m)
        end
        push!(sigpolys, (red, pol, module_pol))
    end
    @debug "done with symbolic pp..."
    return tbl, module_tbl, sigpolys
end     
