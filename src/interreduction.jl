function interreduce(ctx::SigPolynomialΓ{I, M},
                     G::Basis{I, M}) where {I, M}

    unit = Base.one(ctx.po.mo)
    to_reduce = Set((unit, (i, g[1])) for (i, g) in G)
end
