#. PREAMBLE

#= This file defines many term orders. A term order is basically a way to
transform an exponent vector into an "order vector". The ordering is then the
lexicographic ordering on the order vector. The specific application of symbolic
integration requires very baroque term order. Thanks to Julia's JIT compilation,
even baroque monomial order can be compiled rather efficiently.

The type of the exponents is not made explicit, we can choose any signed integer type.
=#

using StaticArrays

#. Some helpers for SVectors

"""
    srange(v :: StaticVector, ::Val{first}, ::Val{last})

Extract consecutive coefficients from a static vector.
"""
@generated function srange(v :: StaticVector, ::Val{first}, ::Val{last}) where {first, last}
    :(SVector( $([:(v[$i]) for i in first:last]...) ))
end

@generated function _concat(::Size{p}, va :: StaticVector, ::Size{q}, vb :: StaticVector) where {p,q}
    :(SVector{p[1]+q[1]}($([:(va[$i]) for i in 1:p[1]]...), $([:(vb[$i]) for i in 1:q[1]]...)))
end

"""
    concat(va :: StaticVector, vb :: StaticVector)

Concatenate two static vectors into a static vector.
"""
concat(va, vb) = _concat(Size(va), va, Size(vb), vb)


#. Abstract interface


""" Abstract type for term order on monomials with N exponents. Includes term
order on modules (where one or several exponents are used to indicate the
position).

Interface for T <: TermOrder{N}:
    - `ordervector(::T, ::SVector) :: SVector`
        return a static vector on which to perform lexicographic ordering.

    - iscompatible(::T, e::SVector, f::SVector)
        indicates if `e`  and `f` have a common multiple. Only useful for module orders.
"""
abstract type TermOrder{N} end

nvars(t::TermOrder{N}) where N = N

"""
    divides(t::TermOrder{N}, e::SVector{N}, f::SVector{N})

Returns true if and only if the two terms are compatible (that is, in the case of a module order, they live at the same position)
and `f` is a multiple of `e`.
"""
divides(t::TermOrder{N}, e::SVector{N}, f::SVector{N}) where N =
    iscompatible(t, e, f) && all(e .<= f)


""" Abstract type for monomial order in a ring. """
abstract type MonomialOrder{N} <: TermOrder{N} end

iscompatible(::MonomialOrder{N}, e::SVector{N}, f::SVector{N}) where N = true

#. Concrete types

#.. Lexicographic order
struct Lex{N} <: MonomialOrder{N} end
Lex(N) = Lex{N}()

ordervector(::Lex{N}, e::SVector{N}) where N = e
extends_degree(::Lex) = false

#.. Graded reverse lexicographic order
struct Grevlex{N} <: MonomialOrder{N} end
Grevlex(N) = Grevlex{N}()
extends_degree(::Grevlex) = true

# should be compiled statically
ordervector(::Grevlex{N}, e::SVector{N}) where N = insert(deleteat(reverse(-e), N), 1, sum(e))

#.. Weighted grevlex
struct WGrevlex{N} <: MonomialOrder{N}
    weights :: NTuple{N, Int}
end

extends_degree(::WGrevlex) = false
ordervector(o::WGrevlex{N}, e::SVector{N}) where N = ordervector(Grevlex(N), o.weights .* e)

#.. Block order

""" Lexicographic on two blocks """
struct Block{N, O1 <: TermOrder, O2 <: TermOrder} <: TermOrder{N}
    o1 :: O1
    o2 :: O2
end

extends_degree(::Block) = false

Block(o1, o2) = Block{nvars(o1)+nvars(o2), typeof(o1), typeof(o2)}(o1, o2)

Base.:*(o1::TermOrder, o2::TermOrder) = Block(o1, o2)

split(b::Block{N}, e::SVector{N}) where {N} =
    (srange(e, Val(1), Val(nvars(b.o1))), srange(e, Val(nvars(b.o1)+1), Val(N)))

ordervector(b::Block{N}, e::SVector{N}) where N =
    concat(ordervector(b.o1, split(b, e)[1]), ordervector(b.o2, split(b, e)[2]))

iscompatible(b::Block{N}, e::SVector{N}, f::SVector{N}) where N =
    iscompatible(b.o1, split(b, e)[1], split(b, f)[1]) &&
    iscompatible(b.o2, split(b, e)[2], split(b, f)[2])




#. Sort interface

@generated function lt(t::TermOrder{N}, e::SVector{N}, f::SVector{N}) where N
    quote
        oe = ordervector(t, e)
        of = ordervector(t, f)

        $([:(oe[$i] < of[$i] && return true ; oe[$i] > of[$i] && return false) for i in 1:N]...)

        return false
    end
end

# @generated function divides(t::TermOrder{N}, e::SVector{N}, f::SVector{N}) where N
#     quote
#         $([:(e[$i] > f[$i] && return false) for i in 1:N]...)

#         return true
#     end
# end
