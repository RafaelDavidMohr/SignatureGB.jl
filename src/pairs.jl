using DataStructures

const MonSigPair{I, M} = Tuple{M, Tuple{I, M}}
const Pair{I, M} = Tuple{MonSigPair{I, M}, MonSigPair{I, M}}
const Basis{I, M} = Dict{I, Vector{Tuple{M, M}}}
const Syz{I, M} = Dict{I, Vector{M}}

function degree(ctx::SigPolynomialΓ{I, M}, p::MonSigPair{I, M}) where {I, M}
    degree(ctx.po.mo, p[1]) + degree(ctx.po.mo, p[2][2])
end

function new_syz(ctx::SigPolynomialΓ, length)
    I = pos_type(ctx)
    M = eltype(ctx.po.mo)
    Dict([(I(i), M[]) for i in 1:length])
end

function new_basis(ctx::SigPolynomialΓ, length)
    M = eltype(ctx.po.mo)
    Dict([(pos_type(ctx)(i), Tuple{M, M}[]) for i in 1:length])
end

# leadingmonomial(G_pos::SortedDict{M, M}, g::M) where M = G_pos[g]

function new_basis_elem!(ctx::SigPolynomialΓ{I, M},
                         G::Basis{I, M},
                         g::Tuple{I, M}) where {I, M}
    
    push!(G[g[1]], (g[2], leadingmonomial(ctx, g)))
end

function pos(ctx::SigPolynomialΓ{I, M},
             p::Tuple{I, M}) where {I, M}
    
    iszero(p[1]) && return zero(I)
    ctx.ord_indices[p[1]][:position]
end

pos(ctx::SigPolynomialΓ{I, M}, p::MonSigPair{I, M}) where {I, M} = pos(ctx, p[2])

function gettag(ctx::SigPolynomialΓ{I, M},
                p::Tuple{I, M}) where {I, M}

    iszero(p[1]) && return :nil
    ctx.ord_indices[p[1]][:tag]
end

gettag(ctx::SigPolynomialΓ{I, M}, p::MonSigPair{I, M}) where {I, M} = gettag(ctx, p[2])

function pretty_print(ctx::SigPolynomialΓ{I, M}, a::MonSigPair{I, M}) where {I, M}
    "$(Vector{Int}(ctx.po.mo[a[1][1]].exponents)), $(Int(ctx.ord_indices[a[2][1]][:position])), $(Vector{Int}(ctx.po.mo[a[2][2]].exponents))"
end

function pretty_print(ctx::SigPolynomialΓ{I, M}, a::Tuple{I, M}) where {I, M}
    "$(Vector{Int}(ctx.po.mo[a[2]].exponents)), $(Int(ctx.ord_indices[a[1]][:position]))"
end

function nullmonsigpair(ctx::SigPolynomialΓ)
    (zero(mon_type(ctx)), (zero(pos_type(ctx)), zero(mon_type(ctx))))
end

isnull(p::MonSigPair) = iszero(p[2][1])

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
        if !(isnull(a[2])) && !(isnull(b[2]))
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
                lm_sig::M,
                G::Basis{I, M},
                H::Syz{I, M}) where {I, M, SΓ <: SigPolynomialΓ{I, M}}

    pos = sig[1]
    for (i, Gi) in G
        for (j, (g, lm)) in enumerate(Gi)
            g_sig = (i, g)
            g_sig == sig && continue
            m = lcm(ctx.po.mo, lm, lm_sig)
            a = div(ctx.po.mo, m, lm_sig)
            rewriteable_syz(ctx, a, sig, G, H) && continue
            b = div(ctx.po.mo, m, lm)
            (pos, ctx(sig)[:sigratio]) == (i, ctx(g_sig)[:sigratio]) && continue
            rewriteable(ctx, b, g_sig, j, G, H) && continue
            if lt(ctx, (pos, ctx(sig)[:sigratio]), (i, ctx(g_sig)[:sigratio]))
                push!(pairset, ((b, g_sig), (a, sig)))
            else
                push!(pairset, ((a, sig), (b, g_sig)))
            end
        end
    end
end

function pair!(ctx::SΓ,
               pairset::PairSet{I, M, SΓ},
               sig::Tuple{I, M}) where {I, M, SΓ <: SigPolynomialΓ{I, M}}

    iszero(ctx(sig)[:poly]) && return
    push!(pairset, ((ctx.po.mo(one(valtype(ctx.po.mo))), sig), nullmonsigpair(ctx)))
end

#.. Rewrite functions for add rewrite order

function new_rewriter!(ctx::SΓ,
                       pairset::PairSet{I, M, SΓ},
                       sig::Tuple{I, M}) where {I, M, SΓ <: SigPolynomialΓ{I, M}}
    pos, m = sig
    crit = p -> (divides(ctx, sig, mul(ctx, p[1]...)) || (!(isnull(p[2])) && divides(ctx, sig, mul(ctx, p[2]...))))
    for p in pairset
        if crit(p)
            delete!(pairset, p)
        end
    end
end

function rewriteable(ctx::SigPolynomialΓ{I, M},
                     m::M,
                     sig::Tuple{I, M},
                     indx,
                     G::Basis{I, M}) where {I, M}

    msig = mul(ctx.po.mo, m, sig[2])
    pos = sig[1]
    for (g, lm) in view(G[pos], indx + 1:length(G[pos]))
        divides(ctx.po.mo, g, msig) && return true
    end
        
    return false
end

function rewriteable_syz(ctx::SigPolynomialΓ{I, M},
                         m::M,
                         sig::Tuple{I, M},
                         G::Basis{I, M},
                         H::Syz{I, M}) where {I, M}

    msig = mul(ctx, m, sig)
    pos = sig[1]
    for h in H[pos]
        divides(ctx.po.mo, h, msig[2]) && return true
    end
    pos_t = pos_type(ctx)
    for i in filter(j -> ctx.ord_indices[j] < ctx.ord_indices[pos], keys(G))
        for (g, lm) in G[i]
            divides(ctx.po.mo, lm, msig[2]) && return true
        end
    end
    return false
end

function rewriteable(ctx::SigPolynomialΓ{I, M},
                     m::M,
                     sig::Tuple{I, M},
                     indx,
                     G::Basis{I, M},
                     H::Syz{I, M}) where {I, M}

    rewriteable_syz(ctx, m, sig, G, H) || rewriteable(ctx, m, sig, indx, G)
end

# selection

function select_one!(ctx::SΓ,
                     pairs::PairSet{I, M, SΓ};
                     select_both = true) where {I, M, SΓ <: SigPolynomialΓ{I, M}}
    
    pair = pop!(pairs)
    indx = pos(ctx, pair[1])
    if isnull(pair[2]) || !(select_both)
        return mpairset(ctx, [pair[1]]), false, 1, indx
    else
        return mpairset(ctx, [pair[1], pair[2]]), true, 1, indx
    end
end

function select_all_pos_and_degree!(ctx::SΓ,
                                    pairs::PairSet{I, M, SΓ};
                                    select_both = true) where {I, M, SΓ <: SigPolynomialΓ{I, M}}

    nselected = 0
    pair = first(pairs)
    indx = pos(ctx, pair[1])
    if isnull(pair[2])
        return mpairset(ctx, [pair[1]]), false, 1, indx
    end
    selected = mpairset(ctx)
    for p in pairs
        if pos(ctx, p[1]) == indx && degree(ctx, p[1]) == degree(ctx, pair[1])
            push!(selected, first(p))
            select_both && push!(selected, p[2])
            nselected += 1
        else
            break
        end
    end
    selected, select_both, nselected, indx
end 

function select_all_pos!(ctx::SΓ,
                         pairs::PairSet{I, M, SΓ};
                         select_both = true) where {I, M, SΓ <: SigPolynomialΓ{I, M}}

    pair = first(pairs)
    indx = pos(ctx, pair[1])
    if isnull(pair[2])
        return mpairset(ctx, [pair[1]]), false, indx
    end
    selected = mpairset(ctx)
    for p in pairs
        if pos(ctx, p[1]) == indx
            push!(selected, first(p))
            select_both && push!(selected, p[2])
        else
            break
        end
    end
    selected, select_both, indx
end
