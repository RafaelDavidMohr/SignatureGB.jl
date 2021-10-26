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
            # probably need to check that lt(ctx(n, g)) == n*lt(ctx, g)
            if divides(ctx.po.mo, lm, m)
                delta = div(ctx.po.mo, m, lm)
                # @debug "possible reducer $(pretty_print(ctx, (delta, (i, g)))) for $(pretty_print(ctx.po.mo, m))"
                use_max_sig && i == max_sig_pos && degree(ctx, (delta, g_sig)) > sig_degree && continue
                if !(interreduction_step) && (enable_lower_pos_rewrite || i == max_sig_pos)
                    rewriteable(ctx, delta, g_sig, j, G, H) && continue
                end
                if !(interreduction_step) && (isnothing(reducer) || lt(mpairord, (delta, g_sig), reducer))
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
                      interreduction_step = true,
                      enable_lower_pos_rewrite = true) where {I, M <: Integer,
                                                              MS <: Union{MonSigSet{I, M}, Set{MonSigPair{I, M}}},
                                                              SΓ <: SigPolynomialΓ{I, M}}

    if !(interreduction_step)
        todo = Set{M}(vcat([ctx(p...)[:poly].mo for p in pairs]...))
    else
        todo = Set{M}(vcat([mul(ctx.po, ctx(p[2])[:poly], p[1]).mo for p in pairs]...))
    end
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
            if !(interreduction_step)
                union!(todo, ctx(red...)[:poly].mo)
            else
                union!(todo, mul(ctx.po, ctx(red[2])[:poly], red[1]).mo)
            end
        end
    end
    check_sigs = [mul(ctx, p...) for p in pairs]
    sort(collect(done), lt = (a, b) -> lt(ctx.po.mo, a, b), rev = true)
end     
