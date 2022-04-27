mutable struct SymPPData{I, M, T, J}
    tbl::EasyTable{M, J}
    rows::Vector{Tuple{MonSigPair{I, M}, Polynomial{J, T}}}
end

function find_reducer(ctx::SigPolynomialΓ{I, M},
                      G::Basis{I, M},
                      H::Syz{I, M},
                      m::M,
                      all_koszul,
                      curr_indx::I,
                      sig_degree::E;
                      # interreduction_step = false,
                      f5c = false,
                      kwargs...) where {I, M, E}

    if mod_order(ctx) == :SCHREY || mod_order(ctx) == :DPOT
        cond = p -> schrey_degree(ctx, p) <= sig_degree
    elseif mod_order(ctx) == :POT
        cond = p -> index(ctx, p) < curr_indx || degree(ctx, p) <= sig_degree
    else
        cond = p -> degree(ctx, p) <= sig_degree
    end

    reducer = nullmonsigpair(ctx)
    mpairord = mpairordering(ctx)
    for (j, (g, lm)) in enumerate(G)
        if divides(ctx.po.mo, lm, m)
            delta = div(ctx.po.mo, m, lm)
            !(cond((delta, g))) && continue
            if !(f5c) || index(ctx, g) == curr_indx
                rewriteable(ctx, delta, g, j, G, H, all_koszul) && continue
            end
            if isnull(reducer) || Base.Order.lt(mpairord, (delta, g), reducer)
                reducer = (delta, g)
                f5c && index(ctx, g) < curr_indx && break
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
                      curr_indx;
                      are_pairs = true,
                      # interreduction_step = false,
                      f5c = false,
                      kwargs...) where {I, M,
                                          MS <: Union{MonSigSet{I, M}, Set{MonSigPair{I, M}}},
                                          SΓ <: SigPolynomialΓ{I, M}}

    @debug "symbolic preprocessing..."
    get_orig_elem = p -> f5c && index(ctx, p) < curr_indx
    if mod_order(ctx) == :SCHREY || mod_order(ctx) == :DPOT
        sig_degree = maximum(p -> schrey_degree(ctx, p), pairs)
    elseif mod_order(ctx) == :POT
        sig_degree = maximum(p -> degree(ctx, p), filter(p -> index(ctx, p) == curr_indx, pairs))
    else
        sig_degree = maximum(p -> degree(ctx, p), pairs)
    end

    tbl = easytable(M[])
    sigpolys = Tuple{MonSigPair{I, M}, Polynomial{ind_type(tbl), eltype(ctx.po.co)}}[]
    sizehint!(sigpolys, length(pairs))
    done = Set{M}()
    are_pairs && sizehint!(done, length(pairs) >> 1)
    for (i, p) in enumerate(pairs)
        pol = ctx(p..., no_rewrite = get_orig_elem(p)).pol
        are_pairs && iseven(i) && push!(done, bla)
        push!(sigpolys, (p, indexpolynomial(tbl, pol)))
    end
        
    for m in tbl.val
        m in done && continue
        red = find_reducer(ctx, G, H, m, all_koszul, curr_indx, sig_degree,
                           f5c = f5c;
                           kwargs...)
        isnull(red) && continue
        push!(sigpolys, (red, indexpolynomial(tbl, ctx(red..., no_rewrite = get_orig_elem(red)).pol)))
        @debug "found reducer $((red, ctx)) for $(gpair(ctx.po.mo, m))"
    end
    @debug "done with symbolic pp..."
    return SymPPData(tbl, sigpolys)
end     
