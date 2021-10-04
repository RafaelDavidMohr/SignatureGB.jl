using DataStructures

const MonSigPair{I, M} = Tuple{M, Tuple{I, M}}
const Pair{I, M} = Tuple{MonSigPair{I, M}, MonSigPair{I, M}}
const Basis{I, M, MΓ} = Dict{I, SortedSet{M, Ordering{MΓ}}}

function new_basis(ctx::SigPolynomialΓ, length)
    Dict([(pos_type(ctx)(i), minmonomialset(ctx.po.mo)) for i in 1:length])
end

pos(p::MonSigPair{I, M}) where {I, M} = p[2][1]

function pretty_print(ctx::SigPolynomialΓ{I, M}, a::MonSigPair{I, M}) where {I, M}
    "$(Vector{Int}(ctx.po.mo[a[1][1]].exponents)), $(Int(a[2][1])), $(Vector{Int}(ctx.po.mo[a[2][2]].exponents))"
end

function nullmonsigpair(ctx::SigPolynomialΓ)
    (zero(mon_type(ctx)), (zero(pos_type(ctx)), zero(mon_type(ctx))))
end

struct MPairOrdering{SΓ <: SigPolynomialΓ}<:Base.Order.Ordering
    ctx::SΓ
end
mpairordering(ctx::SΓ) where SΓ = MPairOrdering{SΓ}(ctx)

function Base.Order.lt(porder::MPairOrdering{SΓ},
                       a::MonSigPair{I, M},
                       b::MonSigPair{I, M}) where {I, M, SΓ <: SigPolynomialΓ{I, M}}
    lt(porder.ctx, mul(porder.ctx, a...), mul(porder.ctx, b...))
end

struct PairOrdering{SΓ <: SigPolynomialΓ}<:Base.Order.Ordering
    ord::MPairOrdering{SΓ}
end
pairordering(ctx::SΓ) where SΓ = PairOrdering{SΓ}(mpairordering(ctx))

function Base.Order.lt(porder::PairOrdering{SΓ},
                       a::Pair{I, M},
                       b::Pair{I, M}) where {I, M, SΓ <: SigPolynomialΓ{I, M}}
    if mul(porder.ord.ctx, first(a)...) == mul(porder.ord.ctx, first(b)...)
        if !(iszero(pos(a[2]))) && !(iszero(pos(b[2])))
            return Base.Order.lt(porder.ord, a[2], b[2])
        end
    end
    Base.Order.lt(porder.ord, first(a), first(b))
end

const PairSet{I, M, SΓ} = SortedSet{Pair{I, M}, PairOrdering{SΓ}}
const MonSigSet{I, M, SΓ} = SortedSet{MonSigPair{I, M}, MPairOrdering{SΓ}}

function mpairset(ctx::SigPolynomialΓ{I, M},
                  pairs::Vector{MonSigPair{I, M}}) where {I, M}
    SortedSet(pairs, mpairordering(ctx))
end

function mpairset(ctx::SigPolynomialΓ{I, M}) where {I, M}
    mpairset(ctx, MonSigPair{I, M}[])
end

function pairset(ctx::SigPolynomialΓ{I, M},
                 pairs::Vector{Pair{I, M}}) where {I, M}
    SortedSet(pairs, pairordering(ctx))
end

function pairset(ctx::SigPolynomialΓ{I, M}) where {I, M}
    pairset(ctx, Pair{I, M}[])
end

function pairs!(ctx::SΓ,
                pairset::PairSet{I, M, SΓ},
                sig::Tuple{I, M},
                G::Basis{I, M},
                H::Basis{I, M}) where {I, M, SΓ <: SigPolynomialΓ{I, M}}

    pos = sig[1]
    for i in keys(G)
        for _g in G[i]
            g = (i, _g)
            m = lcm(ctx.po.mo, leadingmonomial(ctx, g), leadingmonomial(ctx, sig))
            a = div(ctx.po.mo, m, leadingmonomial(ctx, sig))
            rewriteable_syz(ctx, a, sig, G, H) && continue
            b = div(ctx.po.mo, m, leadingmonomial(ctx, g))
            (pos, ctx(sig)[:sigratio]) == (i, ctx(g)[:sigratio]) && continue
            rewriteable(ctx, b, g, G, H) && continue
            if lt(ctx, (pos, ctx(sig)[:sigratio]), (i, ctx(g)[:sigratio]))
                # @debug "new pair" pretty_print(ctx, (b, g)), pretty_print(ctx, (a, sig))
                push!(pairset, ((b, g), (a, sig)))
            else
                push!(pairset, ((a, sig), (b, g)))
                # @debug "new pair" pretty_print(ctx, (a, sig)), pretty_print(ctx, (b, g))
            end
        end
    end
end

function pair!(ctx::SΓ,
               pairset::PairSet{I, M, SΓ},
               sig::Tuple{I, M}) where {I, M, SΓ <: SigPolynomialΓ{I, M}}

    push!(pairset, ((ctx.po.mo(one(valtype(ctx.po.mo))), sig), nullmonsigpair(ctx)))
end

#.. Rewrite functions for add rewrite order

function new_rewriter!(ctx::SΓ,
                       pairset::PairSet{I, M, SΓ},
                       sig::Tuple{I, M}) where {I, M, SΓ <: SigPolynomialΓ{I, M}}
    pos, m = sig
    crit = p -> (divides(ctx, sig, mul(ctx, p[1]...)) || (!(iszero(p[2][2][1])) && divides(ctx, sig, mul(ctx, p[2]...))))
    for p in pairset
        if crit(p)
            delete!(pairset, p)
        end
    end
end

function rewriteable(ctx::SigPolynomialΓ{I, M},
                     m::M,
                     sig::Tuple{I, M},
                     G::Basis{I, M}) where {I, M}

    msig = mul(ctx.po.mo, m, sig[2])
    pos = sig[1]
    # can we make this iteration better?
    flag = false
    # for g in G[pos]
    #     lt(ctx.po.mo, sig[2], g) && divides(ctx.po.mo, g, msig) && return true
    # end
    for g in inclusive(G[pos], searchsortedafter(G[pos], sig[2]), lastindex(G[pos]))
        divides(ctx.po.mo, g, msig) && return true
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
        for _g in G[i]
            g = (i, _g)
            divides(ctx.po.mo, leadingmonomial(ctx, g), msig[2]) && return true
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

# selection

function select_one!(ctx::SΓ,
                     pairs::PairSet{I, M, SΓ}) where {I, M, SΓ <: SigPolynomialΓ{I, M}}
    
    pair = pop!(pairs)
    if iszero(pos(pair[2]))
        return mpairset(ctx, [pair[1]]), false
    else
        @debug "selected" pretty_print(ctx, pair[1]), pretty_print(ctx, pair[2])
        return mpairset(ctx, [pair[1], pair[2]]), true
    end
end

function select_all_pos!(ctx::SΓ,
                         pairs::PairSet{I, M, SΓ}) where {I, M, SΓ <: SigPolynomialΓ{I, M}}

    if iszero(pos(pair[2]))
        return mpairset(ctx, [pair[1]]), false
    end
    pos = first(pairs)[1][2][1]
    selected = mpairset(ctx)
    for p in pairs
        if p[1][2][1] == pos
            push!(selected, first(p))
            push!(selected, p[2])
        else
            break
        end
    end
    selected
end
