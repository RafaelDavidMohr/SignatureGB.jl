# This is a small scale experiment as an alternative to Sage's (and Nemo's)
# parent model to allow for easier low-level operations.
#
# For example, a monomial is represented as a vector (or rather a static vector)
# but to manipulate it, you probably want to know more: what is the term order?
# what variables are module position? This is store in a "parent" variable.
#
# So typically, a monomial will be represented by a structure with two fields:
# the actual exponents, and the parent. But say that you have an array with many
# monomials, all sharing the same parent. Julia will probably box them (because
# of the pointer to the parent) and the information of the parent is very
# repetitive.
#
# So instead, we define an abstract type Context{T}, which is meant to
# "interpret" the elements of type T. And when, we want to store a element
# together with its parent, we enclose is in a Γpair. For low-level code, we
# just carry around the context and never use Γpairs.

abstract type Context{T} end
Base.eltype(::Context{T}) where T = T

struct Γpair0{T, Γ<:Context{T}}
    ctx::Γ
    dat::T
end
const Γpair{Γ, T} = Γpair0{T, Γ}

gpair(ctx::Γ, dat) where {T, Γ<:Context{T}} = Γpair{Γ, T}(ctx, dat)

# Default conversion, but some conversion may require more information about the context.
(ctx::Context{T})(x...) where {T} = eltype(ctx)(x...)

#.. Sorting interface

# To make it possible to sort arrays of type T, define lt(::Context{T}, ::T, ::T)
# Of course, you can also define directly lt(::T, ::T) but it is not always possible.

struct Ordering{Γ<:Context}<:Base.Order.Ordering
    ctx::Γ
end
order(ctx::Γ) where Γ = Ordering{Γ}(ctx)

function Base.Order.lt(order::Ordering{Γ}, a, b) where {Γ<:Context}
    lt(order.ctx, a, b)
end
