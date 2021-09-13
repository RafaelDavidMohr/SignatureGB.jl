#. HASHTABLES

#.. EasyTable
# Building upon Julia's Dict

mutable struct EasyTable{T, I <: Unsigned}
    val::Vector{T}
    rev::Dict{T, I}
    columnindices::Vector{I}

    function EasyTable{T, I}() where {T, I}
        new(T[], Dict{T, I}())
    end
end

Base.getindex(table::EasyTable{T}, i) where T = table.val[i]
Base.length(table::EasyTable) = length(table.val)

@inline find(table::EasyTable{T, I}, v::T) where {T, I} = get(table.rev, v, zero(I))
@inline function findorpush!(table::EasyTable{T, I}, v::T) where {T, I}
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

#.. MonomialHashTable
# Mostly for fun, may not be a good candidate for GB computations

mutable struct MonomialHashTable{N, E, I <: Unsigned, B <: Unsigned}
    val::Vector{Monomial{N, E}}
    bitmasks::Vector{B}
    idx::Vector{I}

    max_powers::MVector{N, E}
    min_powers::MVector{N, E}
    bitmask_powers::SVector{N, E}
    mask::I
    size::Int
    maxloop::Int

    function MonomialHashTable{N, E, I, B}() where {N, E, I, B}
        tsize = 16
        @assert 2*tsize <= typemax(I)
        zs = SVector{N, E}(zeros(E, N))
        new(Monomial{N, E}[], B[], zeros(Int, 2*tsize),
            zs, zs, zs, tsize-1, 0, 4)
    end
end

Base.@propagate_inbounds Base.getindex(table::MonomialHashTable, i) = table.val[i]
Base.length(table::MonomialHashTable) = length(table.val)

index1(table::MonomialHashTable{N, E, I}, v::Monomial{N, E}) where {N, E, I} = 2*( (hash(v) % I)&table.mask ) + 1
index2(table::MonomialHashTable{N, E, I}, v::Monomial{N, E}) where {N, E, I} = 2*( ((hash(v) >> 32) % I)&table.mask ) + 2

function find(table::MonomialHashTable{N, E, I}, v::Monomial{N, E}) where {N, E, I}
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


function rehash!(table::MonomialHashTable{N, E, I}) where {N, E, I}
    #@warn "REHASH $(length(table)) elems, $(length(table.idx)) index table"

    table.idx = zeros(I, 2*length(table.idx))
    table.maxloop += 2
    table.mask = 2*table.mask + 1

    for n in 1:length(table.val)
        register!(table, I(n))
    end
end

function register!(table::MonomialHashTable{N, E, I}, n::I) where {N, E, I}
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


function findorpush!(table::MonomialHashTable{N, E, I, B}, v::Monomial{N, E}) where {N, E, I, B}
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
    remask_cond = false
    @inbounds for i in 1:N
        e = v.exponents[i]
        if e > table.max_powers[i]
            remask_cond = true
            table.max_powers[i] = e
        end
        if e < table.min_powers[i]
            remask_cond = true
            table.min_powers[i] = e
        end
    end
    remask_cond && remask!(table)
    push!(table.bitmasks, bitmask(v, table.bitmask_powers, masktype = B))
    table.size += 1
    n = I(table.size)

    register!(table, n)
    return n
end

function remask!(table::MonomialHashTable{N, E}) where {N, E}

    avg_int = (x, y) -> floor((x + y) / 2)
    table.bitmask_powers = @inbounds SVector{N, E}([avg_int(table.max_powers[i], table.min_powers[i]) for i in 1:N])
    table.bitmasks = broadcast(v -> bitmask(v, table.bitmask_powers), table.val)
end

#. INDEXED MONOMIALS

mutable struct IxMonomialΓ{I<:Unsigned, N, E, B}<:MonomialContext{I}
    ctx::MonomialContext{Monomial{N, E}}
    table::MonomialHashTable{N, E, I, B}
end

# need to change this?
const IxPolynomialΓ{I, T, moΓ <: IxMonomialΓ{I}, coΓ} = PolynomialΓ{I, T, moΓ, coΓ}

function ixmonomialctx(moctx=nothing; indices=UInt32, mask_type=UInt32, kwargs...)
    if isnothing(moctx)
        moctx = monomialctx(;kwargs...)
    end
    return IxMonomialΓ{indices, params(moctx)..., mask_type}(moctx, MonomialHashTable{params(moctx)..., indices, mask_type}())
end

(ctx::IxMonomialΓ{I, N, E, B})(x::Monomial{N, E}) where {I, N, E, B} = findorpush!(ctx.table, ctx.ctx(x))
(ctx::IxMonomialΓ{I})(i::I) where I = i
(ctx::IxMonomialΓ)(x::AA.MPolyElem) = findorpush!(ctx.table, ctx.ctx(x))

Base.@propagate_inbounds Base.getindex(ctx::IxMonomialΓ{I}, i::I) where I = ctx.table[i]

function lt(ix::IxMonomialΓ{I}, a::I, b::I) where I
    lt(ix.ctx, ix[a], ix[b])
end

function indexmonomials(ix::IxMonomialΓ{I, N, E}, p::Polynomial{M, T}) where {I, N, E, M <: Monomial{N, E}, T}
    return Polynomial{I, T}([ix(m) for m in p.mo], p.co)
end

function unindexmonomials(ix::IxMonomialΓ{I, N, E}, p::Polynomial{I, T}) where {I, N, E, T}
    return Polynomial{Monomial{N, E}, T}([ix[i] for i in p.mo], p.co)
end


#.. Monomial interface

variables(ctx::IxMonomialΓ) = variables(ctx.ctx)
nvars(ctx::IxMonomialΓ) = nvars(ctx.ctx)

termorder(ctx::IxMonomialΓ) = termorder(ctx.ctx)
exponents(ctx::IxMonomialΓ{I}, i::I) where I = exponents(ctx.ctx, ctx[i])

mul(ctx::IxMonomialΓ{I}, i::I, j::I) where I = ctx(mul(ctx.ctx, ctx[i], ctx[j]))
div(ctx::IxMonomialΓ{I}, i::I, j::I) where I = ctx(div(ctx.ctx, ctx[i], ctx[j]))
lcm(ctx::IxMonomialΓ{I}, i::I, j::I) where I = ctx(lcm(ctx.ctx, ctx[i], ctx[j]))
function divides(ctx::IxMonomialΓ{I, N},
                 i::I,
                 j::I) where {I, N}

    # (bitcheck(ctx.table.bitmasks[i], ctx.table.bitmasks[j], Val(N))
     iszero(ctx.table.bitmasks[i]  & (~ ctx.table.bitmasks[j])) && divides(ctx.ctx, ctx[i], ctx[j])
end
    
