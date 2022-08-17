using DataStructures

const MonSigPair{I, M} = Tuple{M, SigHash{I, M}}
const Pair{I, M} = Tuple{MonSigPair{I, M}, MonSigPair{I, M}}
struct Basis{I, M}
    sigs::Vector{SigHash{I, M}}
    lms::Vector{M}
    by_index::Dict{I, Vector{M}}
end
const Syz{I, M} = Vector{SigHash{I, M}}

function contains_unit(ctx::SigPolynomialΓ{I, M}, Gsigs::Vector{SigHash{I, M}}) where {I, M}
    any(sig -> degree(ctx.po.mo, leadingmonomial(ctx, sig)) == 0, Gsigs)
end

function poly_reduce(gb::Vector{P},
                     p::P,
                     R) where {P <: AA.MPolyElem}

    J = Singular.Ideal(R, gb)
    J.isGB = true
    q = reduce(p, J)
    return q
end

function filter_basis_by_indices!(ctx::SigPolynomialΓ{I, M},
                                  G::Basis{I, M},
                                  criterion) where {I, M}

    to_delete = findall(sig -> criterion(sig[1]), G.sigs)
    deleteat!(G.sigs, to_delete)
    deleteat!(G.lms, to_delete)
    for i in keys(G.by_index)
        if criterion(i)
            delete!(G.by_index, i)
        end
    end
end
    
function delete_indices!(ctx::SigPolynomialΓ{I, M},
                         G::Basis{I, M},
                         node_ids::I) where {I, M}

    criterion = index_hash -> index_hash in node_ids
    filter_basis_by_indices!(ctx, G, criterion)
end

struct MPairOrdering{SΓ <: SigPolynomialΓ}<:Base.Order.Ordering
    ord::SigOrdering{SΓ}
end

struct PairOrdering{SΓ <: SigPolynomialΓ}<:Base.Order.Ordering
    ord::MPairOrdering{SΓ}
end

const KoszulQueue{I, M, SΓ} = MutableBinaryHeap{SigHash{I, M}, SigOrdering{SΓ}}
# const PairSet{I, M, SΓ} = SortedSet{Pair{I, M}, PairOrdering{SΓ}}
const PairSet{I, M} = Vector{Pair{I, M}}
const MonSigSet{I, M, SΓ} = Set{MonSigPair{I, M}}

function new_basis(ctx::SigPolynomialΓ{I, M}) where {I, M}
    Basis(SigHash{I, M}[], M[], Dict([(i, M[]) for i in keys(ctx.sgb_nodes) if !isone(i)]))
end

Base.length(G::Basis) = Base.length(G.sigs)

new_syz(ctx::SigPolynomialΓ{I, M}) where {I, M} = SigHash{I, M}[]

function gb_size(ctx::SigPolynomialΓ{I, M}, G_sigs::Vector{SigHash{I, M}}) where {I, M}

    isempty(G_sigs) ? 0 : sum([length(ctx(g).pol) for g in G_sigs])
end

function new_basis_elem!(basis::Basis{I, M},
                         sig::SigHash{I, M},
                         lm::M) where {I, M}

    push!(basis.sigs, sig)
    push!(basis.lms, lm)
    if sig[1] in keys(basis.by_index)
        push!(basis.by_index[sig[1]], lm)
    else
        basis.by_index[sig[1]] = [lm]
    end
end

function new_basis_elem!(ctx::SigPolynomialΓ{I, M},
                         basis::Basis{I, M},
                         sig::SigHash{I, M}) where {I, M}
    new_basis_elem!(basis, sig, leadingmonomial(ctx, sig))
end

function Base.show(io::IO,
                   a::Tuple{MonSigPair{I, M}, SX}) where {I, M, SX <: SigPolynomialΓ{I, M}}
    pair = a[1]
    ctx = a[2]
    print(io, (convert(Vector{Int}, exponents(ctx.po.mo, pair[1])),
               (Int(sort_id(ctx, pair[2])), Int(pair[2][1]), convert(Vector{Int}, exponents(ctx.po.mo, pair[2][2])))))
end

function sort_id(ctx::SigPolynomialΓ{I, M}, p::MonSigPair{I, M}) where {I, M}
    sort_id(ctx, p[2])
end

function degree(ctx::SigPolynomialΓ{I, M}, p::MonSigPair{I, M}) where {I, M}
    degree(ctx.po.mo, p[1]) + degree(ctx.po.mo, p[2][2])
end

function schrey_degree(ctx::SigPolynomialΓ{I, M}, p::MonSigPair{I, M}) where {I, M}
    degree(ctx.po.mo, p[1]) + degree(ctx.po.mo, p[2][2]) + degree(ctx.po.mo, ctx.lms[p[2][1]])
end

tag(ctx::SigPolynomialΓ{I, M}, p::MonSigPair{I, M}) where {I, M} = tag(ctx, p[2])

function nullmonsigpair(ctx::SigPolynomialΓ)
    (zero(mon_type(ctx)), (zero(pos_type(ctx)), zero(mon_type(ctx))))
end

isnull(p::MonSigPair) = iszero(p[2][1])

mpairordering(ctx::SΓ) where SΓ = MPairOrdering{SΓ}(sigordering(ctx))

# TODO: check if this is used outside the matrix constructor anywhere
function Base.Order.lt(porder::MPairOrdering{SΓ},
                       a::MonSigPair{I, M},
                       b::MonSigPair{I, M}) where {I, M, SΓ <: SigPolynomialΓ{I, M}}
    amul, bmul = mul(porder.ord.ctx, a...), mul(porder.ord.ctx, b...)
    if amul == bmul
        return a[2][2] < b[2][2]
    end
    Base.Order.lt(porder.ord, amul, bmul)
end

pairordering(ctx::SΓ) where SΓ = PairOrdering{SΓ}(mpairordering(ctx))
function Base.Order.lt(porder::PairOrdering{SΓ},
                       a::Pair{I, M},
                       b::Pair{I, M}) where {I, M, SΓ <: SigPolynomialΓ{I, M}}
    if mul(porder.ord.ord.ctx, first(a)...) == mul(porder.ord.ord.ctx, first(b)...)
        if !(isnull(a[2])) && !(isnull(b[2]))
            return Base.Order.lt(porder.ord, a[2], b[2])
        end
    end
    Base.Order.lt(porder.ord, first(a), first(b))
end

function koszul_syz(ctx::SigPolynomialΓ{I, M},
                    a::SigHash{I, M},
                    b::SigHash{I, M}) where {I, M}

    # sig_a = mul(ctx, leadingmonomial(ctx, b), a)
    # sig_b = mul(ctx, leadingmonomial(ctx, a), b)

    # if lt(ctx, sig_a, sig_b)
    #     return sig_b
    # end
    # return sig_a
    return mul(ctx, leadingmonomial(ctx, b), a)
end

function check!(K::KoszulQueue{I, M, SΓ},
                a::Pair{I, M}) where {I, M, SΓ <: SigPolynomialΓ{I, M}}

    ordering = K.ordering
    ctx = ordering.ctx
    pair_sig = mul(ctx, first(a)...)
    while true
        if !(isempty(K))
            koszul_sig = first(K)
            if Base.lt(ordering, koszul_sig, pair_sig)
                pop!(K)
                continue         
            elseif koszul_sig == pair_sig
                return true
            end
        end
        !(isnull(a[2])) && push!(K, koszul_syz(ctx, a[1][2], a[2][2]))
        return false
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
    # SortedSet(pairs, pairordering(ctx))
    pairs
end

function pairset(ctx::SigPolynomialΓ{I, M}) where {I, M}
    pairset(ctx, Pair{I, M}[])
end

function koszul_queue(ctx::SigPolynomialΓ{I, M}) where {I, M}
    MutableBinaryHeap(sigordering(ctx), SigHash{I, M}[])
end

function pair!(ctx::SΓ,
               pairset::PairSet{I, M},
               sig::SigHash{I, M}) where {I, M, SΓ <: SigPolynomialΓ{I, M}}

    !(iszero(ctx(sig).pol)) && push!(pairset, ((one(ctx.po.mo), sig), nullmonsigpair(ctx)))
end

function pairs!(ctx::SΓ,
                pairset::PairSet{I, M},
                sig::SigHash{I, M},
                lm_sig::M,
                G::Basis{I, M},
                H::Syz{I, M};
                f5c = false,
                kwargs...) where {I, M, SΓ <: SigPolynomialΓ{I, M}}

    index_key = sig[1]
    for (j, g) in enumerate(G.sigs)
        !(are_compatible(ctx, sig, g)) && continue
        lm = G.lms[j]
        index_key == g[1] && ctx(sig).sigratio == ctx(g).sigratio && continue
        m = lcm(ctx.po.mo, lm, lm_sig)
        m == mul(ctx.po.mo, lm, lm_sig) && continue
        a = div(ctx.po.mo, m, lm_sig)
        @debug "considering pair $(gpair(ctx.po.mo, a)), $(sort_id(ctx, sig))"
        if rewriteable_syz(ctx, a, sig, H)
            @debug "rewritten by syz criterion"
            continue
        end
        b = div(ctx.po.mo, m, lm)
        if !(f5c) || g[1] == index_key
            rewriteable(ctx, b, g, j, G, H) && continue
        end
        if lt(ctx, (index_key, ctx(sig).sigratio), (g[1], ctx(g).sigratio))
            @debug "new pair $(((b, g), ctx)), $(((a, sig), ctx))"
            push!(pairset, ((b, g), (a, sig)))
        else
            @debug "new pair $(((a, sig), ctx)), $(((b, g), ctx))"
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
    for g in G.sigs[indx + 1:end]
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

function rewriteable_kosz(ctx::SigPolynomialΓ{I, M},
                          m::M,
                          sig::SigHash{I, M},
                          G::Basis{I, M}) where {I, M}

    msig = mul(ctx, m, sig)
    for i in keys(G.by_index)
        !(are_compatible(ctx, msig, unitvector(ctx, i))) && continue
        sort_id(ctx, i) >= sort_id(ctx, msig) && continue
        for lm in G.by_index[i]
            if divides(ctx.po.mo, lm, msig[2])
                @debug "by koszul criterion"
                return true
            end
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
                       pairset::PairSet{I, M},
                       sig::SigHash{I, M}) where {I, M, SΓ <: SigPolynomialΓ{I, M}}
    pos, m = sig
    crit = p -> (divides(ctx, sig, mul(ctx, p[1]...)) || (!(isnull(p[2])) && divides(ctx, sig, mul(ctx, p[2]...))))
    if !(iszero(ctx(sig).pol))
        crit2 = p -> sort_id(ctx, sig) < sort_id(ctx, p[1]) && divides(ctx.po.mo, leadingmonomial(ctx, sig), mul(ctx, p[1]...)[2])
    else
        crit2 = p -> false
    end
    to_delete = Int[]
    for (i, p) in enumerate(pairset)
        if crit(p)
            @debug "deleting $((p[1], ctx)), $((p[2], ctx))"
            push!(to_delete, i)
        end
        if mod_order(ctx) == :DPOT && crit2(p)
            push!(to_delete, i)
        end
    end
    deleteat!(pairset, to_delete)
end

function select!(ctx::SΓ,
                 G::Basis{I, M},
                 K::KoszulQueue{I, M, SΓ},
                 pairs::PairSet{I, M},
                 cond::Val{S},
                 all_koszul;
                 select_both = true,
                 kwargs...) where {I, M, SΓ <: SigPolynomialΓ{I, M}, S}

    @debug "selecting pairs..."
    @logmsg Verbose2 "" add_row = true
    nselected = 0
    npairs = length(pairs)
    pair = first(pairs)
    node_id = pair[1][2][1]
    sig_degree = degree(ctx, pair[1])
    are_pairs = false
    selected = mpairset(ctx)
    
    if S == :one
        # cond = p -> nselected == 0
        error("selecting one pair at a time is currently not supported. Select must be one of :deg_and_pos or :pos")
    elseif S == :deg_and_pos
        cond = p -> p[1][2][1] == node_id && degree(ctx, p[1]) == sig_degree
    elseif S == :pos
        cond = p -> p[1][2][1] == node_id
    elseif S == :deg
        cond = p -> are_compatible(ctx, p[1][2][1], node_id) && degree(ctx, p[1]) == sig_degree
    elseif S == :schrey_deg
        schrey_deg = schrey_degree(ctx, pair[1])
        @logmsg Verbose2 "" sugar_deg = schrey_deg
        cond = p -> are_compatible(ctx, p[1][2][1], node_id) && schrey_degree(ctx, p[1]) == schrey_deg
    elseif S == :schrey_deg_and_pos
        schrey_deg = schrey_degree(ctx, pair[1])
        @logmsg Verbose2 "" sugar_deg = schrey_deg
        cond = p -> p[1][2][1] == node_id && schrey_degree(ctx, p[1]) == schrey_deg
    else
        error("Select method must be one of :deg_and_pos, :schrey_deg or :pos")
    end

    
    while !(isempty(pairs))
        if !(cond(first(pairs)))
            break
        end
        p = popfirst!(pairs)
        if !(all_koszul)
            if check!(K, p)
                continue
            end
        else
            rewriteable_kosz(ctx, p[1]..., G) && continue
        end
        
        push!(selected, first(p))
        nselected += 1
        if select_both && !(isnull(p[2]))
            are_pairs = true
            push!(selected, p[2])
        end
    end

    @logmsg Verbose2 "" sig_degree nselected npairs
    @debug string("selected:\n", ["$((p, ctx))\n" for p in selected]...)
    selected, sig_degree, are_pairs
end
