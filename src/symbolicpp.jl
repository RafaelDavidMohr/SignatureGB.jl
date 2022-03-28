# TODO: make this work for non degree based orderings
monomialset(ctx::MonomialContext{M}, mons::Vector{M}) where M = SortedSet(mons, Base.Order.ReverseOrdering(order(ctx)))
monomialset(ctx::MonomialContext{M}) where M = monomialset(ctx, M[])
minmonomialset(ctx::MonomialContext{M}) where M = SortedSet(M[], order(ctx))

function find_reducer(ctx::SigPolynomialΓ{I, M},
                      G::Basis{I, M},
                      H::Syz{I, M},
                      m::M,
                      all_koszul,
                      max_sig_index::I,
                      sig_degree::E;
                      interreduction_step = false,
                      f5c = false,
                      kwargs...) where {I, M, E}

    if mod_order(ctx) == :SCHREY
        cond = p -> schrey_degree(ctx, p) <= sig_degree
    elseif mod_order(ctx) == :POT
        cond = p -> index(ctx, p) < max_sig_index || degree(ctx, p) <= sig_degree
    else
        cond = p -> degree(ctx, p) <= sig_degree
    end
    
    reducer = nothing
    mpairord = mpairordering(ctx)
    for (j, (g, lm)) in enumerate(G)
        if divides(ctx.po.mo, lm, m)
            delta = div(ctx.po.mo, m, lm)
            !(cond((delta, g))) && continue
            if !(interreduction_step) && (!(f5c) || index(ctx, g) == max_sig_index)
                rewriteable(ctx, delta, g, j, G, H, all_koszul) && continue
            end
            if !(interreduction_step) && (isnothing(reducer) || Base.Order.lt(mpairord, (delta, g), reducer))
                reducer = (delta, g)
            end
            if interreduction_step && delta != Base.one(ctx.po.mo)
                return (delta, g)
            end
        end
    end
    return reducer
end

function symbolic_pp!(ctx::SΓ,
                      pairs::MS,
                      G::Basis{I, M},
                      H::Syz{I, M},
                      all_koszul;
                      are_pairs = true,
                      interreduction_step = false,
                      f5c = false,
                      kwargs...) where {I, M,
                                          MS <: Union{MonSigSet{I, M}, Set{MonSigPair{I, M}}},
                                          SΓ <: SigPolynomialΓ{I, M}}

    @debug "symbolic preprocessing..."
    max_sig_index = maximum(p -> index(ctx, p), pairs)
    get_orig_elem = p -> interreduction_step || (f5c && index(ctx, p) < max_sig_index)
    if mod_order(ctx) == :SCHREY
        sig_degree = maximum(p -> schrey_degree(ctx, p), pairs)
    elseif mod_order(ctx) == :POT
        sig_degree = maximum(p -> degree(ctx, p), filter(p -> index(ctx, p) == max_sig_index, pairs))
    else
        sig_degree = maximum(p -> degree(ctx, p), pairs)
    end
    todo = Set{M}(vcat([ctx(p..., no_rewrite = get_orig_elem(p)).pol.mo for p in pairs]...))
    if are_pairs
        done = Set{M}([mul(ctx.po.mo, p[1], leadingmonomial(ctx, p[2])) for p in pairs])
    else
        done = Set(M[])
    end
    
    while todo != done
        for m in todo
            m in done && continue
            push!(done, m)
            red = find_reducer(ctx, G, H, m, all_koszul, max_sig_index, sig_degree,
                               interreduction_step = interreduction_step,
                               f5c = f5c;
                               kwargs...)
            isnothing(red) && continue
            push!(pairs, red)
            @debug "found reducer $((red, ctx)) for $(gpair(ctx.po.mo, m))"
            union!(todo, ctx(red..., no_rewrite = get_orig_elem(red)).pol.mo)
        end
    end
    sort(collect(done), lt = (a, b) -> lt(ctx.po.mo, a, b), rev = true)
end     
