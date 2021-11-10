monomialset(ctx::MonomialContext{M}, mons::Vector{M}) where M = SortedSet(mons, Base.Order.ReverseOrdering(order(ctx)))
monomialset(ctx::MonomialContext{M}) where M = monomialset(ctx, M[])
minmonomialset(ctx::MonomialContext{M}) where M = SortedSet(M[], order(ctx))

function find_reducer(ctx::SigPolynomialΓ{I, M},
                      G::Basis{I, M},
                      H::Syz{I, M},
                      m::M;
                      use_max_sig = false,
                      max_sig_pos = zero(pos_type(ctx)),
                      sig_degree = zero(exponenttype(ctx.po.mo)),
                      interreduction_step = false,
                      enable_lower_pos_rewrite = true) where {I, M}

    reducer = nothing
    mpairord = mpairordering(ctx)
    for (i, Gi) in G
        for (j, (g, lm)) in enumerate(Gi)
            g_sig = (i, g)
            if divides(ctx.po.mo, lm, m)
                delta = div(ctx.po.mo, m, lm)
                use_max_sig && ctx.ord_indices[i][:position] == max_sig_pos && degree(ctx, (delta, g_sig)) > sig_degree && continue
                if !(interreduction_step) && (enable_lower_pos_rewrite || ctx.ord_indices[i][:position] == max_sig_pos)
                    rewriteable(ctx, delta, g_sig, j, G, H) && continue
                end
                if !(interreduction_step) && (isnothing(reducer) || Base.Order.lt(mpairord, (delta, g_sig), reducer))
                    reducer = (delta, g_sig)
                end
                if interreduction_step && delta != Base.one(ctx.po.mo)
                    return (delta, g_sig)
                end
            end
        end
    end
    return reducer
end

function symbolic_pp!(ctx::SΓ,
                      pairs::MS,
                      G::Basis{I, M},
                      H::Syz{I, M};
                      use_max_sig = false,
                      sig_degree = zero(exponenttype(ctx.po.mo)),
                      max_sig_pos = zero(pos_type(ctx)),
                      are_pairs= true,
                      interreduction_step = false,
                      enable_lower_pos_rewrite = true) where {I, M <: Integer,
                                                              MS <: Union{MonSigSet{I, M}, Set{MonSigPair{I, M}}},
                                                              SΓ <: SigPolynomialΓ{I, M}}

    get_orig_elem = p -> interreduction_step || (!(enable_lower_pos_rewrite) && pos(ctx, p) < max_sig_pos)
    todo = Set{M}(vcat([ctx(p..., orig_elem = get_orig_elem(p))[:poly].mo for p in pairs]...))
    if are_pairs
        done = Set{M}([mul(ctx.po.mo, p[1], leadingmonomial(ctx, p[2])) for p in pairs])
    else
        done = Set(M[])
    end
    
    while todo != done
        for m in todo
            m in done && continue
            push!(done, m)
            red = find_reducer(ctx, G, H, m,
                               use_max_sig = use_max_sig,
                               max_sig_pos = max_sig_pos,
                               sig_degree = sig_degree,
                               interreduction_step = interreduction_step,
                               enable_lower_pos_rewrite = enable_lower_pos_rewrite)
            isnothing(red) && continue
            push!(pairs, red)
            union!(todo, ctx(red..., orig_elem = get_orig_elem(red))[:poly].mo)
        end
    end
    sort(collect(done), lt = (a, b) -> lt(ctx.po.mo, a, b), rev = true)
end     
