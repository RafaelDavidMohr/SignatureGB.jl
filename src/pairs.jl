using Dictionaries
using DataStructures

struct PairOrdering{SΓ <: SigPolynomialΓ}<:Base.Order.Ordering
    ctx::SΓ
end
pairordering(ctx::SΓ) where SΓ = PairOrdering{SΓ}(ctx)

function Base.Order.lt(porder::PairOrdering{SΓ}, a, b) where {SΓ <: SigPolynomialΓ}
    lt(porder.ctx, mul(porder.ctx, a...), mul(porder.ctx, b...))
end

const Basis{I, M} = SlicedInd{I, M}
const PairSet{I, M, SΓ} = SortedSet{Tuple{M, Tuple{I, M}}, PairOrdering{SΓ}}

function pairset(ctx::SigPolynomialΓ{I, M},
                 pairs::Vector{Tuple{M, Tuple{I, M}}}) where {I, M}
    SortedSet(pairs, pairordering(ctx))
end

function pairset(ctx::SigPolynomialΓ{I, M}) where {I, M}
    SortedSet(Tuple{M, Tuple{I, M}}[], pairordering(ctx))
end

function pairs!(ctx::SΓ,
                pairset::PairSet{I, M, SΓ},
                sig::Tuple{I, M},
                G::Basis{I, M},
                H::Basis{I, M}) where {I, M, SΓ <: SigPolynomialΓ{I, M}}

    for g in G
        m = lcm(ctx.po.mo, leadingmonomial(ctx, g), leadingmonomial(ctx, sig))
        a = div(ctx.po.mo, m, leadingmonomial(ctx, sig))
        rewriteable_syz(ctx, a, sig, G, H) && continue
        b = div(ctx.po.mo, m , leadingmonomial(ctx, g))
        rewriteable(ctx, b, g, G, H) && continue
        if lt(ctx, ctx(a, sig)[:sigratio], ctx(b, g)[:sigratio])
            push!(pairset, (b, g))
        else
            push!(pairset, (a, sig))
        end
    end
end

function pair!(ctx::SΓ,
               pairset::PairSet{I, M, SΓ},
               sig::Tuple{I, M}) where {I, M, SΓ <: SigPolynomialΓ{I, M}}

    push!(pairset, (ctx.po.mo(one(valtype(ctx.po.mo))), sig))
end

#.. Rewrite functions for add rewrite order

function rewriteable(ctx::SigPolynomialΓ{I, M},
                     m::M,
                     sig::Tuple{I, M},
                     G::Basis{I, M}) where {I, M}

    msig = mul(ctx, m, sig)
    pos = sig[1]
    # can we make this iteration better?
    curr = iterate(G[pos], gettoken(G[pos], sig[2])[2][2])
    while !(isnothing(curr))
        (n, tk) = curr
        divides(ctx.po.mo, n, msig[2]) && return true
        curr = iterate(G[pos], tk)
    end
    return false
end

function rewriteable_syz(ctx::SigPolynomialΓ{I, M},
                         m::M,
                         sig::Tuple{I, M},
                         G::Basis{I, M},
                         H::Basis{I, M}) where {I, M}

    msig = mul(ctx, m, sig)
    pos = sig[1]
    for h in H[pos]
        divides(ctx.po.mo, h, msig[2]) && return true
    end
    pos_t = pos_type(ctx)
    for i in pos_t(1):pos_t(pos - 1)
        for g in G[i]
            check_sig = (i, g)
            divides(ctx.po.mo, leadingmonomial(ctx, check_sig), msig[2]) && return true
        end
    end
    return false
end

function rewriteable(ctx::SigPolynomialΓ{I, M},
                     m::M,
                     sig::Tuple{I, M},
                     G::Basis{I, M},
                     H::Basis{I, M}) where {I, M}

    rewriteable_syz(ctx, m, sig, G, H) || rewriteable(ctx, m, sig, G)
end
