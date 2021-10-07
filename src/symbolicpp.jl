monomialset(ctx::MonomialContext{M}, mons::Vector{M}) where M = SortedSet(mons, Base.Order.ReverseOrdering(order(ctx)))
monomialset(ctx::MonomialContext{M}) where M = monomialset(ctx, M[])
minmonomialset(ctx::MonomialContext{M}) where M = SortedSet(M[], order(ctx))

function find_reducer(ctx::SigPolynomialΓ{I, M},
                      G::Basis{I, M},
                      H::Syz{I, M},
                      m::M) where {I, M}

    reducers = mpairset(ctx)
    for i in keys(G)
        for (g, lm) in G[i]
            g_sig = (i, g)
            # probably need to check that lt(ctx(n, g)) == n*lt(ctx, g)
            if divides(ctx.po.mo, lm, m)
                delta = div(ctx.po.mo, m, lm)
                rewriteable(ctx, delta, g_sig, G, H) && continue
                push!(reducers, (delta, g_sig))
            end
        end
    end
    isempty(reducers) && return nothing
    pop!(reducers)
end

function symbolic_pp!(ctx::SΓ,
                      pairs::MonSigSet{I, M, SΓ},
                      G::Basis{I, M},
                      H::Syz{I, M};
                      are_pairs=true) where {I, M <: Integer, SΓ <: SigPolynomialΓ{I, M}}

    todo = Set(vcat([ctx(p[1], p[2])[:poly].mo for p in pairs]...))
    if are_pairs
        done = Set([leadingmonomial(ctx(p[1], p[2])[:poly]) for p in pairs])
    else
        done = Set(M[])
    end

    while todo != done
        for m in todo
            m in done && continue
            push!(done, m)
            red = find_reducer(ctx, G, H, m)
            isnothing(red) && continue
            push!(pairs, red)
            union!(todo, ctx(red[1], red[2])[:poly].mo)
        end
    end
    sort(collect(done), lt = (a, b) -> lt(ctx.po.mo, a, b), rev = true)
end     
