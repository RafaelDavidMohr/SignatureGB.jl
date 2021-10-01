monomialset(ctx::MonomialContext{M}, mons::Vector{M}) where M = SortedSet(mons, Base.Order.ReverseOrdering(order(ctx)))
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

    rewrite_checks_time = 0.0
    reducers = mpairset(ctx)
    for g in G
        n = leadingmonomial(ctx, g)
        # probably need to check that lt(ctx(n, g)) == n*lt(ctx, g)
        if divides(ctx.po.mo, n, m)
            delta = div(ctx.po.mo, m, n)
            @debug "found possible reducer:" pretty_print(ctx, (delta, g))
            rewr = @timed rewriteable(ctx, delta, g, G, H)
            rewrite_checks_time += rewr.time
            if rewr.value
                @debug "it is rewriteable"
                continue
            end
            push!(reducers, (delta, g))
        end
    end
    isempty(reducers) && return nothing, rewrite_checks_time
    pop!(reducers), rewrite_checks_time
end

function symbolic_pp!(ctx::SΓ,
                      pairs::MonSigSet{I, M, SΓ},
                      G::Basis{I, M},
                      H::Basis{I, M};
                      are_pairs=true) where {I, M <: Integer, SΓ <: SigPolynomialΓ{I, M}}

    rewrite_checks_time = 0.0
    todo = monomialset(ctx.po.mo, vcat([ctx(p[1], p[2])[:poly].mo for p in pairs]...))
    if are_pairs
        done = monomialset(ctx.po.mo, [leadingmonomial(ctx(p[1], p[2])[:poly]) for p in pairs])
    else
        done = monomialset(ctx.po.mo)
    end

    while todo != done
        for m in todo
            m in done && continue
            push!(done, m)
            red, new_time = find_reducer(ctx, G, H, m)
            rewrite_checks_time += new_time
            isnothing(red) && continue
            push!(pairs, red)
            union!(todo, ctx(red[1], red[2])[:poly].mo)
        end
    end
    done, rewrite_checks_time
end     
