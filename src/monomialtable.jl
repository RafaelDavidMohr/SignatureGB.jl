#. HASHTABLES

#.. EasyTable
# Building upon Julia's Dict

mutable struct EasyTable{T, I <: Unsigned}
    val :: Vector{T}
    rev :: Dict{T, I}
    columnindices :: Vector{I}

    function EasyTable{T, I}() where {T, I}
        new(T[], Dict{T, I}())
    end
end

Base.getindex(table :: EasyTable{T}, i) where T = table.val[i]
Base.length(table :: EasyTable) = length(table.val)

@inline find(table :: EasyTable{T, I}, v :: T) where {T, I} = get(table.rev, v, zero(I))
@inline function findorpush!(table :: EasyTable{T, I}, v :: T) where {T, I}
    n = find(table, v)
    if n > 0
        return n
    else
        push!(table.val, v)
        n = I(length(table.val))
        table.rev[v] = n
        return n
    end
end

#.. CuckooTable
# Mostly for fun, may not be a good candidate for GB computations

mutable struct CuckooTable{T, I <: Unsigned}
    val :: Vector{T}
    idx :: Vector{I}

    mask :: I
    size :: Int
    maxloop :: Int

    function CuckooTable{T, I}() where {T, I}
        tsize = 16
        @assert 2*tsize <= typemax(I)
        new(T[], zeros(Int, 2*tsize), tsize-1, 0, 4)
    end
end

Base.@propagate_inbounds Base.getindex(table :: CuckooTable{T}, i) where T = table.val[i]
Base.length(table :: CuckooTable) = length(table.val)

index1(table :: CuckooTable{T, I}, v) where {T, I} = 2*( (hash(v) % I)&table.mask ) + 1
index2(table :: CuckooTable{T, I}, v) where {T, I} = 2*( ((hash(v) >> 32) % I)&table.mask ) + 2

function find(table :: CuckooTable{T, I}, v :: T) where {T, I}
    @inbounds begin
        n = table.idx[index1(table, v)]
        if n > 0 && table[n] == v
            return n
        end

        n = table.idx[index2(table, v)]
        if n > 0 && table[n] == v
            return n
        end
        return zero(I)
    end
end


function rehash!(table :: CuckooTable{T, I}) where {T, I}
    #@warn "REHASH $(length(table)) elems, $(length(table.idx)) index table"

    table.idx = zeros(I, 2*length(table.idx))
    table.maxloop += 2
    table.mask = 2*table.mask + 1

    for n in 1:length(table.val)
        register!(table, I(n))
    end
end

function register!(table :: CuckooTable{T, I}, n :: I) where {T, I}
    #@warn "register $n"
    @inbounds for _ in 1:table.maxloop
        i1 = index1(table, table[n])
        #@warn "push $n in i1=$i1"
        n, table.idx[i1] = table.idx[i1], n
        if iszero(n)
            return
        end

        i2 = index2(table, table[n])
        #@warn "push $n in i2=$i2"
        n, table.idx[i2] = table.idx[i2], n
        if iszero(n)
            return
        end
    end

    rehash!(table)
end


function findorpush!(table :: CuckooTable{T, I}, v :: T) where {T, I}
    @inbounds begin
        n = table.idx[index1(table, v)]
        if n > 0 && table[n] == v
            return n
        end

        n = table.idx[index2(table, v)]
        if n > 0 && table[n] == v
            return n
        end
    end

    #@warn "Insert $v"
    push!(table.val, v)
    table.size += 1
    n = I(table.size)

    register!(table, n)
    return n
end



#. INDEXED MONOMIALS

mutable struct IxMonomialΓ{I<:Unsigned, M, Γ<:MonomialContext{M}}<:MonomialContext{I}
    ctx::Γ
    table::CuckooTable{M, I}
end

const IxPolynomialΓ{I, T, moΓ <: IxMonomialΓ{I}, coΓ} = PolynomialΓ{I, T, moΓ, coΓ}

function ixmonomialctx(moctx=nothing; indices=UInt32, kwargs...)
    if isnothing(moctx)
        moctx = monomialctx(;kwargs...)
    end
    return IxMonomialΓ{indices, eltype(moctx), typeof(moctx)}(moctx, CuckooTable{eltype(moctx), indices}())
end

(ctx::IxMonomialΓ{I, M, Γ})(x) where {I, M, Γ} = findorpush!(ctx.table, ctx.ctx(x))
(ctx::IxMonomialΓ{I})(i::I) where I = i
(ctx::IxMonomialΓ)(x::AA.MPolyElem) = findorpush!(ctx.table, ctx.ctx(x))

Base.@propagate_inbounds Base.getindex(ctx::IxMonomialΓ{I}, i::I) where I = ctx.table[i]

function lt(ix::IxMonomialΓ{I}, a::I, b::I) where I
    lt(ix.ctx, ix[a], ix[b])
end

function indexmonomials(ix::IxMonomialΓ{I, M}, p::Polynomial{M, T}) where {I, M, T}
    return Polynomial{I, T}([ix(m) for m in p.mo], p.co)
end

function unindexmonomials(ix::IxMonomialΓ{I, M}, p::Polynomial{I, T}) where {I, M, T}
    return Polynomial{M, T}([ix[i] for i in p.mo], p.co)
end


#.. Monomial interface

variables(ctx::IxMonomialΓ) = variables(ctx.ctx)
nvars(ctx::IxMonomialΓ) = nvars(ctx.ctx)

termorder(ctx::IxMonomialΓ) = termorder(ctx.ctx)
exponents(ctx::IxMonomialΓ{I}, i::I) where I = exponents(ctx.ctx, ctx[i])

mul(ctx::IxMonomialΓ{I}, i::I, j::I) where I = ctx(mul(ctx.ctx, ctx[i], ctx[j]))
div(ctx::IxMonomialΓ{I}, i::I, j::I) where I = ctx(div(ctx.ctx, ctx[i], ctx[j]))
lcm(ctx::IxMonomialΓ{I}, i::I, j::I) where I = ctx(lcm(ctx.ctx, ctx[i], ctx[j]))
