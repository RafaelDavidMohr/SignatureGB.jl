monomialset(ctx::MonomialContext{M}, mons::Vector{M}) where M = SortedSet(mons, ReverseOrder(order(ctx)))
monomialset(ctx::MonomialContext{M}) where M = monomialset(ctx, M[])

function Base.union!(s::SortedSet{T}, new::Vector{T}) where T
    for n in new
        push!(s, n)
    end
end

function find_reducer(ctx::SigPolynomialΓ{I, M},
                      G::Basis{I, M},
                      H::Basis{I, M},
                      m::M) where {I, M}

    reducers = pairset(ctx)
    for g in G
        n = leadingmonomial(ctx, g)
        # probably need to check that lt(ctx(n, g)) == n*lt(ctx, g)
        if divides(ctx.po.mo, n, m)
            delta = div(ctx.po.mo, m, n)
            rewriteable(ctx, delta, g, G, H) && continue
            push!(reducers, (n, g))
        end
    end
    isempty(reducers) && return nothing
    pop!(reducers)
end

function symbolic_pp!(ctx::SigPolynomialΓ{I, M},
                      pairs::PairSet{I, M},
                      G::Basis{I, M},
                      H::Basis{I, M}) where {I, M <: Integer}

    todo = monomialset(ctx.po.mo, [ctx(p[1], p[2])[:polynomial].monomials... for p in pairs])
    done = monomialset(ctx.po.mo)

    while todo != done
        for m in todo
            m in done && continue
            push!(done, m)
            red = find_reducer(ctx, G, H, m)
            isnothing(red) && continue
            push!(pairs, red)
            union!(todo, ctx(red[1], red[2])[:polynomial].monomials)
        end
    end
end     
