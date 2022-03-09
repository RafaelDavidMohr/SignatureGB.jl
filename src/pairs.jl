using DataStructures

const MonSigPair{I, M} = Tuple{M, SigHash{I, M}}
const Pair{I, M} = Tuple{MonSigPair{I, M}, MonSigPair{I, M}}
const Basis{I, M} = Vector{Tuple{SigHash{I, M}, M}}
const Syz{I, M} = Vector{SigHash{I, M}}

struct MPairOrdering{SΓ <: SigPolynomialΓ}<:Base.Order.Ordering
    ord::SigOrdering{SΓ}
end

struct PairOrdering{SΓ <: SigPolynomialΓ}<:Base.Order.Ordering
    ord::MPairOrdering{SΓ}
end

const KoszulQueue{I, M, SΓ} = MutableBinaryHeap{SigHash{I, M}, SigOrdering{SΓ}}
const PairSet{I, M, SΓ} = SortedSet{Pair{I, M}, PairOrdering{SΓ}}
const MonSigSet{I, M, SΓ} = Set{MonSigPair{I, M}}

new_basis(ctx::SigPolynomialΓ{I, M}) where {I, M} = Tuple{SigHash{I, M}, M}[]
new_syz(ctx::SigPolynomialΓ{I, M}) where {I, M} = SigHash{I, M}[]

function new_basis_elem!(ctx::SigPolynomialΓ{I, M},
                         basis::Basis{I, M},
                         sig::SigHash{I, M}) where {I, M}

    push!(basis, (sig, leadingmonomial(ctx, sig)))
end

function Base.show(io::IO,
                   a::Γpair0{MonSigPair{I, M}, SX}) where {I, M, SX <: SigPolynomialΓ{I, M}}
    pair = a.dat
    Base.show(io, (gpair(ctx.po.mo, pair[1]), gpair(ctx, pair[2])))
end


function degree(ctx::SigPolynomialΓ{I, M}, p::MonSigPair{I, M}) where {I, M}
    degree(ctx.po.mo, p[1]) + degree(ctx.po.mo, p[2][2])
end

index(ctx::SigPolynomialΓ{I, M}, p::MonSigPair{I, M}) where {I, M} = index(ctx, p[2])

tag(ctx::SigPolynomialΓ{I, M}, p::MonSigPair{I, M}) where {I, M} = tag(ctx, p[2])

function nullmonsigpair(ctx::SigPolynomialΓ)
    (zero(mon_type(ctx)), (zero(pos_type(ctx)), zero(mon_type(ctx))))
end

isnull(p::MonSigPair) = iszero(p[2][1])

mpairordering(ctx::SΓ) where SΓ = MPairOrdering{SΓ}(sigordering(ctx))

function Base.Order.lt(porder::MPairOrdering{SΓ},
                       a::MonSigPair{I, M},
                       b::MonSigPair{I, M}) where {I, M, SΓ <: SigPolynomialΓ{I, M}}
    amul, bmul = mul(porder.ctx, a...), mul(porder.ctx, b...)
    if amul == bmul
        # TODO: this might break stuff
        return b[2][2] < a[2][2]
    end
    lt(porder.ord, amul, bmul)
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

function koszul_syz(ctx::SigPolynomialΓ{I, M},
                    a::SigHash{I, M},
                    b::SigHash{I, M}) where {I, M}

    sig_a = mul(ctx, leadingmonomial(ctx, b), a)
    sig_b = mul(ctx, leadingmonomial(ctx, a), b)

    if lt(ctx, sig_a, sig_b)
        return sig_b
    end
    return sig_a
end

function check!(K::KoszulQueue{I, M, SΓ},
                a::Pair{I, M}) where {I, M, SΓ <: SigPolynomialΓ{I, M}}

    ordering = K.ordering
    ctx = ordering.ctx
    koszul_sig = first(K)
    pair_sig = mul(ctx, first(a)...)
    while !(isempty(K))
        if Base.lt(ordering, koszul_sig, pair_sig)
            pop!(K)
            koszul_sig = first(K)
        elseif koszul_sig == pair_sig
            return true
        else
            !(isnull(a[2])) && push!(K, koszul_syz(ctx, a[1][2], a[2][2]))
            return false
        end
    end
end

function mpairset(ctx::SigPolynomialΓ{I, M},
                  pairs::Vector{MonSigPair{I, M}}) where {I, M}
    Set(pairs)
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

function koszul_queue(ctx::SigPolynomialΓ{I, M}) where {I, M}
    MutableBinaryHeap(sigordering(ctx), SigHash{I, M}[])
end

function pair!(ctx::SΓ,
               pairset::PairSet{I, M, SΓ},
               sig::SigHash{I, M}) where {I, M, SΓ <: SigPolynomialΓ{I, M}}

    !(iszero(ctx(sig).pol)) && push!(pairset, ((one(ctx.po.mo), sig), nullmonsigpair(ctx)))
end

function pairs!(ctx::SΓ,
                pairset::PairSet{I, M, SΓ},
                sig::SigHash{I, M},
                lm_sig::M,
                G::Basis{I, M},
                H::Syz{I, M};
                enable_lower_index_rewrite = true) where {I, M, SΓ <: SigPolynomialΓ{I, M}}

    index_key = sig[1]
    for (j, (g, lm)) in enumerate(G)
        index_key == g[1] && ctx(sig).sigratio == ctx(g).sigratio && continue
        m = lcm(ctx.po.mo, lm, lm_sig)
        m == mul(ctx.po.mo, lm, lm_sig) && continue
        a = div(ctx.po.mo, m, lm_sig)
        rewriteable_syz(ctx, a, sig, H) && continue
        b = div(ctx.po.mo, m, lm)
        if enable_lower_index_rewrite || i == index_key
            rewriteable(ctx, b, g, j, G, H) && continue
        end
        if lt(ctx, (index_key, ctx(sig).sigratio), (g[1], ctx(g).sigratio))
            push!(pairset, ((b, g), (a, sig)))
        else
            push!(pairset, ((a, sig), (b, g)))
        end
    end
end

function rewriteable(ctx::SigPolynomialΓ{I, M},
                     m::M,
                     sig::SigHash{I, M},
                     indx,
                     G::Basis{I, M}) where {I, M}

    msig = mul(ctx, m, sig)
    for (g, lm) in G[indx + 1:end]
        divides(ctx, g, msig) && return true
    end
        
    return false
end

function rewriteable_syz(ctx::SigPolynomialΓ{I, M},
                         m::M,
                         sig::SigHash{I, M},
                         H::Syz{I, M}) where {I, M}

    msig = mul(ctx, m, sig)
    for h in H
        if divides(ctx, h, msig)
            return true
        end
    end

    return false
end

function rewriteable(ctx::SigPolynomialΓ{I, M},
                     m::M,
                     sig::SigHash{I, M},
                     indx,
                     G::Basis{I, M},
                     H::Syz{I, M}) where {I, M}

    rewriteable_syz(ctx, m, sig, H) || rewriteable(ctx, m, sig, indx, G)
end

function new_rewriter!(ctx::SΓ,
                       pairset::PairSet{I, M, SΓ},
                       sig::SigHash{I, M}) where {I, M, SΓ <: SigPolynomialΓ{I, M}}
    pos, m = sig
    crit = p -> (divides(ctx, sig, mul(ctx, p[1]...)) || (!(isnull(p[2])) && divides(ctx, sig, mul(ctx, p[2]...))))
    for p in pairset
        if crit(p)
            delete!(pairset, p)
        end
    end
end

function select!(ctx::SΓ,
                 K::KoszulQueue{I, M, SΓ},
                 pairs::PairSet{I, M, SΓ},
                 cond::Val{S};
                 select_both = true) where {I, M, SΓ <: SigPolynomialΓ{I, M}, S}

    pair = pop!(pairs)
    indx = pos(ctx, pair[1])
    sig_degree = degree(ctx, pair[1])
    are_pairs = false
    selected = mpairset(ctx, [pair[1]])
    if select_both && !(isnull(pair[2]))
        push!(selected, pair[2])
        are_pairs = true
    end
    
    if S == :one
        cond = p -> false
    elseif S == :deg_and_pos
        cond = p -> pos(ctx, p[1]) == indx && degree(ctx, p[1]) == sig_degree
    elseif S == :pos
        cond = p -> pos(ctx, p[1]) == indx
    else
        error("Select method must be one of :one, :deg_and_pos or :pos")
    end
    
    while !(isempty(pairs))
        if !(cond(first(pairs)))
            break
        end
        p = pop!(pairs)
        if check!(K, p)
            continue
        end
        push!(selected, first(p))
        select_both && push!(selected, p[2])
    end
    selected, are_pairs, nselected, sig_degree
end
