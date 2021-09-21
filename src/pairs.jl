using Dictionaries
using DataStructures

struct PairOrdering{SΓ <: SigPolynomialΓ}<:Base.Order.Ordering
    ctx::SΓ
end
pairordering(ctx::SΓ) where SΓ = PairOrdering{SΓ}(ctx)

function Base.order.lt(porder::PairOrdering{SΓ}, a, b) where {SΓ <: SigPolynomialΓ}
    lt(porder.ctx, mul(porder.ctx, a...), mul(porder.ctx, b...))
end

const Basis{I, M} = SlicedInd{I, M}
const PairSet{I, M, SΓ} = BinaryHeap{Tuple{M, Tuple{I, M}}, PairOrdering{SΓ}}

function rewriteable(ctx::SigPolynomialΓ{I, M},
                     m::M,
                     sig::Tuple{I, M},
                     G::Basis{I, M}) where {I, M}

    msig = mul(ctx, m, sig)
    pos = sig[1]
    curr = iterate(G[pos], gettoken(G[pos], sig)[2][2])
    while !(isnothing(curr))
        (n, tk) = curr
        divis(ctx.po.mo, n, msig[2]) && return true
        curr = iterate(G[pos], tk)
    end
    return false
end

function rewriteable_syz(ctx::SigPolynomialΓ{I, M},
                         m::M,
                         sig::Tuple{I, M},
                         H::Basis{I, M}) where {I, M}

    msig = mul(ctx, m, sig)
    pos = sig[1]
    for h in H[pos]
        divis(ctx.po.mo, h, msig[2]) && return true
    end
    return false
end

function rewriteable(ctx::SigPolynomialΓ{I, M},
                     m::M,
                     sig::Tuple{I, M},
                     G::Basis{I, M},
                     H::Basis{I, M}) where {I, M}

    rewriteable_syz(ctx, m, sig, H) || rewriteable(ctx, m, sig, G)
end
