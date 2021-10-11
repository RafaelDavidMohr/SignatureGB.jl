monomialset(ctx::MonomialContext{M}, mons::Vector{M}) where M = SortedSet(mons, Base.Order.ReverseOrdering(order(ctx)))
monomialset(ctx::MonomialContext{M}) where M = monomialset(ctx, M[])
minmonomialset(ctx::MonomialContext{M}) where M = SortedSet(M[], order(ctx))

function find_reducer(ctx::SigPolynomialΓ{I, M},
                      G::Basis{I, M},
                      H::Syz{I, M},
                      m::M,
                      use_max_sig = false,
                      max_sig = (zero(I), zero(M))) where {I, M}

    reducers = MonSigPair{I, M}[]
    for (i, Gi) in G
        for (g, lm) in Gi
            g_sig = (i, g)
            # probably need to check that lt(ctx(n, g)) == n*lt(ctx, g)
            if divides(ctx.po.mo, lm, m)
                delta = div(ctx.po.mo, m, lm)
                # @debug "possible reducer $(pretty_print(ctx, (delta, (i, g)))) for $(pretty_print(ctx.po.mo, m))"
                use_max_sig && !(lt(ctx, mul(ctx, delta, g_sig), max_sig)) && continue
                rewriteable(ctx, delta, g_sig, G, H) && continue
                push!(reducers, (delta, g_sig))
            end
        end
    end
    isempty(reducers) && return nothing
    mpairord = mpairordering(ctx)
    sort!(reducers, lt = (a, b) -> Base.Order.lt(mpairord, a, b))
    first(reducers)
end

function symbolic_pp!(ctx::SΓ,
                      pairs::MonSigSet{I, M, SΓ},
                      G::Basis{I, M},
                      H::Syz{I, M};
                      use_max_sig = false,
                      are_pairs= true) where {I, M <: Integer, SΓ <: SigPolynomialΓ{I, M}}

    todo = Set(vcat([ctx(p[1], p[2])[:poly].mo for p in pairs]...))
    if are_pairs
        done = Set([mul(ctx.po.mo, p[1], leadingmonomial(ctx, p[2])) for p in pairs])
    else
        done = Set(M[])
    end

    if use_max_sig
        max_sig = mul(ctx, last(pairs)...)
    else
        max_sig = (zero(I), zero(M))
    end
    
    while todo != done
        for m in todo
            m in done && continue
            push!(done, m)
            red = find_reducer(ctx, G, H, m,
                               use_max_sig,
                               max_sig)
            isnothing(red) && continue
            push!(pairs, red)
            union!(todo, ctx(red[1], red[2])[:poly].mo)
        end
    end
    check_sigs = [mul(ctx, p...) for p in pairs]
    sort(collect(done), lt = (a, b) -> lt(ctx.po.mo, a, b), rev = true)
end     
