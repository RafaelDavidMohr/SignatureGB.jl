
#. Abstract type for coefficients with a special type in which we perform the addmul operation
# Coefficients are stored in T, while addmul is done in Tbuf

"""
Expect:
    - Base.isone(::T) :: Bool
    - Base.iszero(::T) :: Bool
    - add(::NmodLikeΓ{T}, ::T, ::T) :: T
    - mul(::NmodLikeΓ{T}, ::T, ::T) :: T
    - inv(::NmodLikeΓ{T}, ::T) :: T
    - submul(::NmodLikeΓ{T, Tbuf}, ::Tbuf, ::T, ::T) :: Tbuf
    - normal(::NmodLikeΓ{T, Tbuf}, ::Tbuf) :: Tbuf
    - inflate(::NmodLikeΓ{T, Tbuf}, ::T) :: Tbuf
    - deflate(::NmodLikeΓ{T, Tbuf}, ::Tbuf) :: T
"""
abstract type NmodLikeΓ{T, Tbuf}<:Context{T} end

inflate(::NmodLikeΓ{T, Tbuf}, x :: T) where {T, Tbuf} = Tbuf(x)
deflate(::NmodLikeΓ{T, Tbuf}, x :: Tbuf) where {T, Tbuf} = x%T

#. Z/nZ

#.. Abstract type

abstract type NmodΓ{T<:Unsigned, Tbuf<:Unsigned}<:NmodLikeΓ{T,Tbuf} end

(ctx::NmodΓ)(a::AA.ResElem) = ctx(a.data)
abstractalgebra(ctx :: NmodΓ) = Nemo.NmodRing(UInt64(ctx.char))

#.. 32-bit modulus and 64-bit buffer

mutable struct Nmod32Γ<:NmodΓ{UInt32, UInt64}
    char::UInt32
    maxshift::UInt64

    function Nmod32Γ(char)
        uchar = UInt64(char)
        nbits = 64 - leading_zeros(uchar)
        @assert 2*nbits <= 64

        new(uchar, uchar << leading_zeros(uchar))
    end
end


#... arithmetic operations
# Must implement inv, mul, addmul and normal

function add(ctx::Nmod32Γ, a::UInt32, b::UInt32)
    c0 = a+b
    c1 = c0 - ctx.char
    d = max(c0, c1)
    #@assert d%ctx.char == (a%ctx.char + b%ctx.char)%ctx.char
    return d
end

@inline function addmul(ctx::Nmod32Γ, a::UInt64, b::UInt32, c::UInt32)
    z0 = a + UInt64(b)*UInt64(c)
    z1 = z0 - ctx.maxshift
    z = (z0 < a) ? z1 : z0
    return z
end

@inline function submul(ctx::Nmod32Γ, a::UInt64, b::UInt32, c::UInt32)
    z0 = a - UInt64(b)*UInt64(c)
    z1 = z0 + ctx.maxshift
    z = (z0 > a) ? z1 : z0
    # if (z%ctx.char + (UInt64(b)%ctx.char)*(UInt64(c)%ctx.char)%ctx.char)%ctx.char != a%ctx.char
    #    error((ctx, a, b, c))
    # end
    return z
end

function opp(ctx::Nmod32Γ, a::UInt32)
    @assert ctx.char > a
    return ctx.char - a
end

function inv(ctx::Nmod32Γ, a::UInt32)
    invmod(UInt64(a), UInt64(ctx.char)) % UInt32
end

function mul(ctx::Nmod32Γ, a, b)
    (UInt64(a)*UInt64(b) % ctx.char) % UInt32
end

function normal(ctx::Nmod32Γ, a::UInt64)
    a % ctx.char
end


#.. 32-bit modulus with 128-bits buffer

mutable struct Nmod32xΓ<:NmodΓ{UInt32, UInt128}
    char::UInt32
    twotothe64::UInt32        # 2^64 mod char

    function Nmod32xΓ(char)
        uchar = UInt32(char)
        p = (UInt64(2^32) % uchar)^2 % uchar % UInt32

        new(char, p)
    end
end


#... arithmetic operations
# Must implement inv, mul, submul and normal

function add(ctx::Nmod32xΓ, a::UInt32, b::UInt32)
    c0 = a+b
    c1 = c0 - ctx.char
    d = max(c0, c1)
    #@assert d%ctx.char == (a%ctx.char + b%ctx.char)%ctx.char
    return d
end

@inline function addmul(ctx::Nmod32xΓ, a::UInt128, b::UInt32, c::UInt32)
    z0 = a + UInt128(UInt64(b)*UInt64(c))
    return z0
end


@inline function submul(ctx::Nmod32xΓ, a::UInt128, b::UInt32, c::UInt32)
    z0 = a - UInt128(UInt64(b)*UInt64(c))
    return z0
end

function inv(ctx::Nmod32xΓ, a::UInt32)
    UInt32(invmod(UInt64(a), UInt64(ctx.char)))
end

function mul(ctx::Nmod32xΓ, a::UInt32, b::UInt32)
    UInt32((UInt64(a)*UInt64(b) % ctx.char) % UInt32)
end

function normal(ctx::Nmod32xΓ, a::UInt128)
    return a % ctx.char
    # hi = (a >> 64) % UInt64
    # lo = a % UInt64
    # add(ctx,
    #     ctx.twotothe64 * hi % ctx.char % UInt32,
    #     lo % ctx.char % UInt32)
end
