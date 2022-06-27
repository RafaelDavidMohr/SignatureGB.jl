# of module reps
struct SigPolynomial{M, MM, T, MODT}
    pol::Polynomial{M, T}
    module_rep::Polynomial{MM, T}
    sigratio::M
end

# TODO: no longer needed
mutable struct F5Index{I}
    index::I
    tag::Symbol
end

const SigHash{I, M} = Tuple{I, M}
const SigTable{I, M, MM, T, MODT} = Dict{SigHash{I, M}, SigPolynomial{M, MM, T, MODT}}

mutable struct SigPolynomialΓ{I, M, MM, T, MODT,
                              MΓ<:Context{M}, TΓ<:Context{T},
                              MMΓ<:Context{MM},
                              PΓ<:PolynomialΓ{M, T, MΓ, TΓ},
                              PPΓ<:PolynomialΓ{M, T, MMΓ, TΓ}, MORD}<:Context{SigHash{I, M}}
    po::PΓ
    mod_po::PPΓ
    tbl::SigTable{I, M, MM, T, MODT}
    sgb_nodes::Dict{I, SGBNode{I, M, T}}
    branch_nodes::Vector{I}
    # TODO: need a simpler caching mechanism
    cashed_sigs::Vector{SigHash{I, M}}
    track_module_tags::Vector{Symbol}
    lms::Dict{I, M}
end

struct SigOrdering{SΓ <: SigPolynomialΓ}<:Base.Order.Ordering
    ctx::SΓ
end

function sigpolynomialctx(coefficients;
                          polynomials=nothing,
                          mod_polynomials=nothing,
                          pos_type=UInt16,
                          mod_rep_type=nothing,
                          mod_order=:POT,
                          track_module_tags=Symbol[],
                          kwargs...)
    # here we need to possibly build a seperate module_moctx
    if isnothing(polynomials)
        polynomials = polynomialctx(coefficients; kwargs...)
    end
    monomials = polynomials.mo
    
    if !(isnothing(mod_polynomials))
        error("using a different type of monomials for the module is currently not supported.")
    else
        mod_polynomials = polynomials
        mod_monomials = monomials
    end
    eltpe = SigHash{pos_type, eltype(monomials)}
    mon_type = eltype(monomials)
    tbl = SigTable{pos_type, mon_type, mon_type, eltype(coefficients), mod_rep_type}()
    sgb_nodes = Dict{pos_type, SGBNode{pos_type, eltype(monomials), eltype(coefficients)}}()
    SigPolynomialΓ{pos_type, eltype(monomials),
                   eltype(monomials), eltype(coefficients),
                   mod_rep_type, typeof(monomials),
                   typeof(coefficients), typeof(monomials),
                   typeof(polynomials), typeof(mod_polynomials),
                   mod_order}(polynomials, mod_polynomials, tbl, sgb_nodes,
                              pos_type[], eltpe[], track_module_tags, Dict{pos_type, mon_type}())
end

function Base.Order.lt(order::SigOrdering{SΓ},
                       a::SigHash{I, M},
                       b::SigHash{I, M}) where {I, M, SΓ <: SigPolynomialΓ{I, M}}
    lt(order.ctx, a, b)
end
sigordering(ctx::SΓ) where SΓ = SigOrdering{SΓ}(ctx)

function Base.show(io::IO,
                   a::Γpair0{SigHash{I, M}, SX}) where {I, M, SX <: SigPolynomialΓ{I, M}}
    ctx = a.ctx
    sighash = a.dat
    print(io, (Int(index(ctx, sighash)),
               convert(Vector{Int}, exponents(ctx.po.mo, sighash[2]))))
end

function SigPolynomial(ctx::SigPolynomialΓ{I, M, MM, T, MODT},
                       pol::Polynomial{M, T},
                       module_rep::Polynomial{MM, T},
                       sigratio::M) where {I, M, MM, T, MODT}
    
    SigPolynomial{M, MM, T, MODT}(pol, module_rep, sigratio)
end

pos_type(::SigPolynomialΓ{I}) where {I} = I
mon_type(::SigPolynomialΓ{I, M}) where {I, M} = M
mod_mon_type(::SigPolynomialΓ{I, M, MM}) where {I, M, MM} = MM
coeff_type(::SigPolynomialΓ{I, M, MM, T}) where {I, M, MM, T} = T
function mod_rep_type(::SigPolynomialΓ{I, M, MM, T,
                                       MODT}) where {I, M, MM, T, MODT}
    MODT
end
function mod_order(ctx::SigPolynomialΓ{I, M, MM, T,
                                       MODT, MΓ, TΓ,
                                       MMΓ, PΓ, PPΓ, MORD}) where {I, M, MM, T, MODT, MΓ, TΓ, MMΓ, PΓ, PPΓ, MORD}
    MORD
end
unitvector(ctx::SigPolynomialΓ, i) = (pos_type(ctx)(i), one(ctx.po.mo))
isunitvector(ctx::SigPolynomialΓ{I, M}, a::SigHash{I, M}) where {I, M} = a[2] == one(ctx.po.mo)

tag(ctx::SigPolynomialΓ{I}, i::I) where {I} = ctx.sgb_nodes[i].tag
tag(ctx::SigPolynomialΓ{I, M}, p::SigHash{I, M}) where {I, M} = tag(ctx, p[1])

function new_generator!(ctx::SigPolynomialΓ{I, M, MM, T},
                        parent_id::I,
                        pol::Polynomial{M, T},
                        tag = :f;
                        module_rep = ctx.po([one(ctx.po.mo)], [one(eltype(ctx.po.co))])) where {I, M, MM, T}
    
    new_node = new_node!(parent_id, pol, ctx.sgb_nodes, tag)
    # TODO: Temporary! find a more consistent way to assign sort ids
    assign_sort_ids!(ctx.sgb_nodes)
    sighash = unitvector(ctx, new_node.ID)
    if mod_order(ctx) in [:SCHREY, :DPOT]
        ctx.lms[new_node.ID] = leadingmonomial(pol)
    end
    ctx(sighash, pol, module_rep)
    return new_node.ID
end

function split_on_tag_f!(ctx::SigPolynomialΓ{I, M, MM, T},
                         f_node_id::I,
                         zd_to_insert::Polynomial{M, T}) where {I, M, MM, T}

    new_ids, new_branch_node_ids, new_cleaners = split_on_tag_f!(ctx.sgb_nodes,
                                                                 f_node_id,
                                                                 zd_to_insert)

    module_rep = ctx.po([one(ctx.po.mo)], [one(eltype(ctx.po.co))])
    
    for id in vcat(new_ids, new_cleaners)
        sighash = unitvector(ctx, id)
        pol = ctx.sgb_nodes[id].pol
        if mod_order(ctx) in [:SCHREY, :DPOT]
            ctx.lms[new_node.ID] = leadingmonomial(pol)
        end
        ctx(sighash, pol, copy(module_rep))
    end
    assign_sort_ids!(ctx.sgb_nodes)
    return new_ids, new_branch_node_ids, new_cleaners
end

function sort_id(ctx::SigPolynomialΓ{I, M},
                 a::SigHash{I, M}) where {I, M}

    ctx.sgb_nodes[a[1]].sort_ID
end

# registration functions
function (ctx::SigPolynomialΓ{I, M, MM, T})(sig::SigHash{I, M},
                                            pol::Polynomial{M, T},
                                            module_rep::Polynomial{MM, T}) where {I, M, MM, T}
    # TODO: maybe temporary
    @assert sig[1] in keys(ctx.sgb_nodes)
    if iszero(pol)
        ratio = one(ctx.po.mo)
    else
        ratio = div(ctx.po.mo, sig[2], leadingmonomial(pol))
    end
    val = SigPolynomial(ctx, pol, module_rep, ratio)
    ctx.tbl[sig] = val
end

function (ctx::SigPolynomialΓ{I, M, MM, T})(sig::SigHash{I, M}, pol::Polynomial{M, T}) where {I, M, MM, T}
    ctx(sig, pol, zero(eltype(ctx.mod_po)))
end

Base.getindex(ctx::SigPolynomialΓ{I, M}, sig::SigHash{I, M}) where {I, M} = getindex(ctx.tbl, sig)

# get functions

# WARNING: if sig::Tuple{J, MO} where J != I or MO != M then this will convert sig to a Tuple{I, M}

@inline function (ctx::SigPolynomialΓ{I, M})(sig::SigHash{I, M}) where {I, M}
    ctx.tbl[sig]
end

function (ctx::SigPolynomialΓ{I, M})(m::M, sig::Tuple{I, M}; no_rewrite = false) where {I, M}
    
    key = mul(ctx, m, sig)
    if !(no_rewrite)
        get(ctx.tbl, key) do
            cashed_rewriters = filter(p -> lt(ctx, sig, p) && divides(ctx, p, key), ctx.cashed_sigs)
            if isempty(cashed_rewriters)
                val = ctx.tbl[sig]
                return SigPolynomial(ctx, mul(ctx.po, val.pol, m), mul(ctx.mod_po, val.module_rep, m), val.sigratio)
            else
                # TODO: no need to sort here
                sort!(cashed_rewriters, lt = (p1, p2) -> lt(ctx, p1, p2), rev = true)
                rewr = first(cashed_rewriters)
                @debug "cached rewriter $(gpair(ctx, rewr)) for $(((m, sig), ctx))"
                n = div(ctx.po.mo, key[2], rewr[2])
                val = ctx.tbl[rewr]
                return SigPolynomial(ctx, mul(ctx.po, val.pol, n), mul(ctx.mod_po, val.module_rep, n), val.sigratio)
            end
        end
    else
        val = ctx.tbl[sig]
        return SigPolynomial(ctx, mul(ctx.po, val.pol, m), mul(ctx.mod_po, val.module_rep, m), val.sigratio)
    end
end

# get projection to highest index

function project(ctx::SigPolynomialΓ{I, M, M, T, :highest_index},
                 m::M,
                 sig::SigHash{I, M};
                 kwargs...) where {I, M, T}
    val = ctx(m, sig; kwargs...)
    Polynomial{M, T}(val.module_rep.mo,
                     val.module_rep.co)
end

function project(ctx::SigPolynomialΓ{I, M, M, T, :highest_index},
                 sig::SigHash{I, M}) where {I, M, T}
    project(ctx, one(ctx.po.mo), sig)
end
    
# forwarding of functions on polynomials/monomials

function mul(ctx::SigPolynomialΓ{I, M}, m::M, sig::SigHash{I, M}) where {I, M}
    (sig[1], mul(ctx.po.mo, m, sig[2]))
end

function divides(ctx::SigPolynomialΓ{I, M}, s1::SigHash{I, M}, s2::SigHash{I, M}) where {I, M}
    s1[1] == s2[1] && divides(ctx.po.mo, s1[2], s2[2])
end

@inline leadingmonomial(ctx::SigPolynomialΓ{I, M}, sig::SigHash{I, M}) where {I, M} = leadingmonomial(ctx(sig).pol)

@inline leadingmonomial(ctx::SigPolynomialΓ{I, M}, m::M, sig::SigHash{I, M}; no_rewrite = false) where {I, M} = leadingmonomial(ctx(m, sig, no_rewrite = no_rewrite).pol)

# sorting

function are_compatible(ctx::SigPolynomialΓ{I, M},
                        a::SigHash{I, M},
                        b::SigHash{I, M}) where {I, M}

    are_compatible(ctx.sgb_nodes[a[1]], ctx.sgb_nodes[b[1]])
end

@inline @generated function lt(ctx::SigPolynomialΓ{I, M, MM, T, MODT, MΓ, MMΓ, TΓ, PΓ, PPΓ, MORD},
                               a::SigHash{I, M},
                               b::SigHash{I, M}) where {I, M, MM, T, MODT, MΓ, MMΓ, TΓ, PΓ, PPΓ, MORD}

    # TODO: check if a total ordering on the nodes is a good idea
    if MORD == :POT
        quote
            if a[1] == b[1]
                return lt(ctx.po.mo, a[2], b[2])
            end
            return ctx.sgb_nodes[a[1]].sort_ID < ctx.sgb_nodes[b[1]].sort_ID
        end
    elseif MORD == :DPOT
        quote
            d1 = degree(ctx.po.mo, a[2]) + degree(ctx.po.mo, ctx.lms[a[1]])
            d2 = degree(ctx.po.mo, b[2]) + degree(ctx.po.mo, ctx.lms[b[1]])
            if d1 == d2
                if a[1] == b[1]
                    return lt(ctx.po.mo, a[2], b[2])
                end
                return ctx.sgb_nodes[a[1]].sort_ID < ctx.sgb_nodes[b[1]].sort_ID
            end
            return d1 < d2
        end
    elseif MORD == :TOP
        quote
            if a[2] == b[2]
                return ctx.sgb_nodes[a[1]].sort_ID < ctx.sgb_nodes[b[1]].sort_ID
            end
            return lt(ctx.po.mo, a[2], b[2])
        end
    elseif MORD == :SCHREY
        quote
            c1 = mul(ctx.po.mo, a[2], ctx.lms[a[1]])
            c2 = mul(ctx.po.mo, b[2], ctx.lms[b[1]])
            if c1 == c2
                return ctx.sgb_nodes[a[1]].sort_ID < ctx.sgb_nodes[b[1]].sort_ID
            end
            return lt(ctx.po.mo, c1, c2)
        end
    end
end

# Abstract Algebra

(ctx::SigPolynomialΓ)(i, m::AA.MPolyElem) = (pos_type(ctx)(i), ctx.po.mo(m))
(ctx::SigPolynomialΓ{I, M})(sig::Tuple{I, M}, p::AA.MPolyElem) where {I, M} = ctx(sig, ctx.po(p))

function (R :: AA.MPolyRing)(ctx::SigPolynomialΓ{I, M},
                             sig::Tuple{I, M}) where {I, M}

    R(ctx.po, ctx(sig).pol)
end

# converting a vector of singular polynomials into our own data structures
function setup(I::Vector{P};
               mod_order=:POT,
               mon_order=:GREVLEX,
               modulus=32,
               buffer=64,
               kwargs...) where {P <: AA.MPolyElem}

    R = parent(first(I))
    char = characteristic(R)
    if mon_order == :GREVLEX
        order = Grevlex(Singular.nvars(R))
    else
        error("only grevlex order currently supported")
    end
    if !(mod_order in [:POT, :SCHREY, :DPOT])
        error("only position over term, degree position over term or schreyer order currently supported")
    end
    if modulus != 32
        error("only 32 bit modulus currently supported")
    end
    if !(buffer in [64, 128])
        error("choose a buffer bitsize of either 64 or 128")
    end
    buffer == 64 ? coefficients = Nmod32Γ(char) : coefficients = Nmod32xΓ(char)
    ctx = sigpolynomialctx(coefficients; mod_order = mod_order,
                           order=order, kwargs...)
    T = eltype(coefficients)
    parent_id = zero(pos_type(ctx))
    if mod_rep_type(ctx) in [nothing, :highest_index]
        for f in I
            f_id = new_generator!(ctx, parent_id, ctx.po(f))
            parent_id = f_id
        end
    elseif mod_rep_type(ctx) == :random_lin_comb
        coeffs = rand(zero(T):T(char - 1), Base.length(I))
        for f in I
            f_id = new_generator!(ctx, parent_id, ctx.po(f), module_rep = ctx.po(R(coeffs[i])))
            parent_id = f_id
        end
    end
    branch_node = new_branch_node!(parent_id, ctx.sgb_nodes)
    push!(ctx.branch_nodes, branch_node.ID)
    if mod_order == :SCHREY || mod_order == :DPOT
        # TODO: iterating over the keys is not ideal
        ctx.lms = Dict([(pos_type(ctx)(i), leadingmonomial(ctx, unitvector(ctx, i)))
                        for i in keys(ctx.sgb_nodes) if !(i in ctx.branch_nodes)])
    end
    ctx
end


#- UNUSED CODE -#

function copy_index!(ctx::SigPolynomialΓ{I},
                     index_hash::I) where I

    elem_to_copy = ctx(unitvector(ctx, index_hash))
    new_index_key = new_generator!(ctx, index(ctx, index_hash) + 1, elem_to_copy.pol,
                                   tag(ctx, index_hash), module_rep = elem_to_copy.module_rep)
    for (ind_hash, mon) in keys(ctx.tbl)
        ind_hash != index_hash && continue
        elem_to_copy = ctx((ind_hash, mon))
        ctx((new_index_key, mon), copy(elem_to_copy.pol), copy(elem_to_copy.module_rep))
    end
    return new_index_key
end

# return original generator of higher index than pos if it exists
function orginal_gen_left(ctx::SigPolynomialΓ{I}, index::I) where I

    result = zero(I)
    for (i, v) in ctx.f5_indices
        if v.tag == :f && v.index > index
            if iszero(result) || v.index < ctx.f5_indices[result].index
                result = i
            end
        end
    end
    return result
end

#--- UNUSED CODE/ONLY FOR TESTING ---#

function new_generator_before!(ctx::SigPolynomialΓ{I, M, MM, T},
                               before::SGBNode{I, M, T},
                               pol::Polynomial{M, T},
                               tag = :f;
                               module_rep = ctx.po([one(ctx.po.mo)], [one(eltype(ctx.po.co))])) where {I, M, MM, T}
    
    new_node = insert_before!(before, pol, ctx.sgb_nodes, tag)
    sighash = unitvector(ctx, new_node.ID)
    if mod_order(ctx) in [:SCHREY, :DPOT]
        ctx.lms[new_node.ID] = leadingmonomial(pol)
    end
    ctx(sighash, pol, module_rep)
    return new_node.ID
end
