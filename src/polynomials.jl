#. PREAMBLE
using StaticArrays
using Random
using Singular

import AbstractAlgebra
import Nemo

const AA = AbstractAlgebra

#. MONOMIALS

#.. Abstract context

""" Abstract type for monomial contexts
Must provide:
    - termorder(::MonomialContext{T}) :: TermOrder
    - exponents(::MonomialContext{T}, ::T) :: SVector
    - (::MonomialContext{T})(::SVector)

It is probably interesting to redefine:
    - mul(::MonomialContext{T}, ::T, ::T) :: T
    - div(::MonomialContext{T}, ::T, ::T) :: T
    - lcm(::MonomialContext{T}, ::T, ::T) :: T
    - gcd(::MonomialContext{T}, ::T, ::T) :: T
"""
abstract type MonomialContext{T} <: Context{T} end

ordervector(ctx::Γ, x::T) where {T, Γ<:MonomialContext{T}} =
    ordervector(termorder(ctx), exponents(ctx, x))

divides(ctx::Γ, x::T, y::T) where {T, Γ<:MonomialContext{T}} =
    divides(termorder(ctx), exponents(ctx, x), exponents(ctx, y))

iscompatible(ctx::Γ, x::T, y::T) where {T, Γ<:MonomialContext{T}} =
    iscompatible(termorder(ctx), exponents(ctx, x), exponents(ctx, y))

lt(ctx::Γ, x::T, y::T) where {T, Γ<:MonomialContext{T}} =
    lt(termorder(ctx), exponents(ctx, x), exponents(ctx, y))

function mul(ctx::MonomialContext{T}, x::T, y::T) where {T}
    ctx(exponents(ctx, x)+exponents(ctx, y))
end

function div(ctx::MonomialContext{T}, x::T, y::T) where {T}
    ctx(exponents(ctx, x)-exponents(ctx, y))
end

function lcm(ctx::MonomialContext{T}, x::T, y::T) where {T}
    ctx(max.(exponents(ctx, x), exponents(ctx, y)))
end

function gcd(ctx::MonomialContext{T}, x::T, y::T) where {T}
    ctx(min.(exponents(ctx, x), exponents(ctx, y)))
end


#.. Monomial type

@generated function makehash(::Val{N}, m) where {N}
    rng = MersenneTwister(18121987)
    hash = :( $(UInt64(0)) )
    for i in 1:N
        hash = :($hash + $(rand(rng, UInt))*UInt(m[$i]))
    end
    return hash
end

makehash(m::SVector{N}) where N = makehash(Val(N), m)

# Monomial in N variables with exponent type E
# We require E to be signed because it makes grevlex easier.
# [TODO is that a good reason?]
struct Monomial{N, E<:Signed}
    exponents::SVector{N, E}
    hash :: UInt

    Monomial{N, E}(e, h :: UInt) where {N, E} = new(e, h)
    Monomial{N, E}(e) where {N, E} = new(e, makehash(Val{N}(), e))
    Monomial{N, E}(m :: Monomial) where {N, E} = new(m.exponents, m.hash)
end

Monomial(e) = Monomial{length(e), eltype(e)}(e, makehash(e))

Base.hash(m::Monomial) = m.hash
Base.show(io::IO, m::Monomial) = Base.show(io, convert(Vector{Int}, m.exponents))
Base.isequal(x::Monomial, y::Monomial) = x.exponents == y.exponents

# Compute a bitmask for the monomial M, TODO: make this generated
function bitmask(m::Monomial{N, E}, pwrs::Dict{Int, Vector{E}}; masktype = UInt32) where {N, E<:Signed}
    @inbounds parse(masktype, join(["$(Int(p <= m.exponents[i]))" for i in 1:N for p in pwrs[i]]), base = 2)
end
                  
Base.one(::Type{Monomial{N, E}}) where {N, E} = Monomial{N, E}(SVector{N, E}(zeros(E, N)))
Base.isone(m::Monomial{N, E}) where {N, E} = m == one(typeof(m))

#.. Monomial context

struct MonomialΓ{N, E, O<:TermOrder{N}}<:MonomialContext{Monomial{N, E}}
    order::O
    vars::Vector{String}
end


# Int16 exponents allows for degree 32727, this leaves room for many applications
function monomialctx(;exponents=Int16, order::TermOrder, vars=[], varprefix="x", indexed=false, kwargs...)
    if isempty(vars)
        vars = [varprefix*string(i) for i in 1:nvars(order)]
    end
    mo = MonomialΓ{nvars(order), exponents, typeof(order)}(order, vars)
    if indexed
        return ixmonomialctx(mo; kwargs...)
    else
        return mo
    end
end

params(::MonomialΓ{N, E}) where {N, E} = N, E
exponents(::MonomialΓ{N, E}, m :: Monomial{N, E}) where {N, E}= m.exponents
exponenttype(::MonomialΓ{N, E}) where {N, E} = E
nvars(::MonomialΓ{N}) where N = N
variables(ctx::MonomialΓ) = ctx.vars
termorder(ctx::MonomialΓ) = ctx.order
Base.one(ctx::MonomialΓ) = Base.one(eltype(ctx))

function mul(::MonomialContext{T}, x::T, y::T) where {T<:Monomial}
    T(x.exponents + y.exponents, x.hash + y.hash)
end

function div(::MonomialContext{T}, x::T, y::T) where {T<:Monomial}
    T(x.exponents - y.exponents, x.hash - y.hash)
end

#... AA interoperability

function (ctx :: MonomialContext)(p :: AA.MPolyElem)
    AA.isterm(p) || error("Not a monomial")
    return ctx(AA.exponent_vector(p, 1))
end

function (R :: AA.MPolyRing)(ctx::MonomialContext{M}, m::M) where M
    br = AA.base_ring(R)

    # there may be a shortcut in AA, I haven't looked
    return R([one(AA.base_ring(R))],
             [convert(Vector{Int}, exponents(ctx, m))])
end



#. POLYNOMIALS

#.. Polynomial type

# The AbstractVector interface is useful, for example, to sort the terms
mutable struct Polynomial{M, T}<:AbstractVector{Tuple{M, T}}
    mo::Vector{M}
    co::Vector{T}
end

Base.size(p::Polynomial) = size(p.co)
Base.@propagate_inbounds Base.getindex(p::Polynomial, i...) = (getindex(p.mo, i...), getindex(p.co, i...))
# may not be ideal
Base.@propagate_inbounds Base.getindex(p::Polynomial, r::UnitRange) = [(p.mo[i], p.co[i]) for i in r]
Base.@propagate_inbounds function Base.setindex!(p::Polynomial{M, T}, t::Tuple{M, T}, i...) where {M, T}
    setindex!(p.mo, t[1], i...)
    setindex!(p.co, t[2], i...)
end
Base.Sort.defalg(p::Polynomial) =  Base.DEFAULT_UNSTABLE

Base.isempty(p::Polynomial) = isempty(p.co)
Base.@propagate_inbounds coefficient(p::Polynomial, i) = p.co[i]
Base.@propagate_inbounds monomial(p::Polynomial, i) = p.mo[i]
Base.@propagate_inbounds leadingmonomial(p::Polynomial) = monomial(p, 1)
monomials(p::Polynomial) = p.mo
Base.zero(::Type{Polynomial{M, T}}) where {M, T} = Polynomial(M[], T[])
Base.zero(p::Polynomial) = zero(typeof(p))
Base.iszero(p::Polynomial) = p == zero(p)

ismonic(p::Polynomial) = !isempty(p) && @inbounds isone(coefficient(p, 1))

Base.copy(p::Polynomial) = typeof(p)(copy(p.mo), copy(p.co))

#.. Context

struct PolynomialΓ{M, T, MΓ<:Context{M}, TΓ<:Context{T}}<:Context{Polynomial{M, T}}
    mo::MΓ
    co::TΓ
end


function polynomialctx(coefficients; monomials=nothing, kwargs...)
    if isnothing(monomials)
        monomials = monomialctx(;kwargs...)
    end
    return PolynomialΓ{eltype(monomials), eltype(coefficients), typeof(monomials),
                       typeof(coefficients)}(monomials, coefficients)
end

nvars(ctx::PolynomialΓ) = nvars(ctx.mo)
variables(ctx::PolynomialΓ) = variables(ctx.mo)
termorder(ctx::PolynomialΓ) = termorder(ctx.mo)

function lt(ctx::PolynomialΓ, a, b)
    lt(ctx.mo, leadingmonomial(a), leadingmonomial(b))
end

function lt(ctx::Γ, a::Tuple{M, T}, b :: Tuple{M, T}) where {M, T, Γ<:PolynomialΓ{M, T}}
    lt(ctx.mo, a[1], b[1])
end

function normalize!(ctx::Γ, p::T; onlysort::Bool=false) where {T<:Polynomial, Γ<:Context{T}}
    sort!(p, rev=true, order=order(ctx))
    onlysort && return

    # collapse like terms, remove zeros
    w = 0                   # read and write indices
    r = 1
    lenp = length(p)
    while r <= lenp
        m = monomial(p, r)
        c = coefficient(p, r)

        while true
            r += 1
            if r > lenp || monomial(p, r) != m
                break
            end
            c = add(ctx.co, acc, coefficient(p, r))
        end

        if !iszero(c)
            w += 1
            p[w] = (m, c)
        end
    end

    resize!(p.co, w)
    resize!(p.mo, w)
    sizehint!(p.co, w)
    sizehint!(p.mo, w)

    return
end


function monic!(ctx::TΓ,
                p::Polynomial{M, T}) where {M, T, TΓ <: Context{T}}
    isempty(p) && return
    @inbounds begin
        isone(coefficient(p, 1)) && return

        mult = inv(ctx, coefficient(p, 1))
        for (i, c) in enumerate(p.co)
            p.co[i] = mul(ctx, mult, c)
        end
    end
    return
end

#.. Basic operations

function selectcoefficient(ctx::Γ, p::P, var::Int, exp::Int) where {P <: Polynomial, Γ<:Context{P}}
    newp = ctx([], [])
    for (m, c) in p
        if exponents(ctx.mo, m)[var] == exp
            if exp == 0
                push!(newp.mo, m)
            else
                newm = ctx.mo(setindex(exponents(ctx.mo, m), 0, var))
                push!(newp.mo, newm)
            end
            push!(newp.co, c)
        end
    end
    return newp
end

function add!(ctx::Γ, p::P, q::P) where {P<:Polynomial, Γ<:Context{P}}
    append!(p.co, q.co)
    append!(p.mo, q.mo)
    normalize!(ctx, p)
    return
end

function add(ctx::Γ, p::P, q::P) where {P<:Polynomial, Γ<:Context{P}}
    cp = copy(p)
    add!(ctx, cp, q)
    return cp
end

# Share the coefficient array
function mul(ctx::PolynomialΓ{M, T}, p::Polynomial{M, T}, m::M) where {M, T}
    newmo = [mul(ctx.mo, m, mp) for mp in p.mo]
    eltype(ctx)(newmo, p.co)
end


# The basic operation in symbolic preprocessing
function shift(ctx::PolynomialΓ{M, T}, p :: Polynomial{M, T}, m :: M ;
               targetmonomialctx = ctx.mo) where {M, T}
    delta = div(ctx.mo, m, leadingmonomial(p))
    newmo = Vector{eltype(targetmonomialctx)}(undef, length(p))
    @inbounds for (i, q) in enumerate(p.mo)
        newmo[i] = targetmonomialctx(mul(ctx.mo, q, delta))
    end
    return Polynomial{eltype(targetmonomialctx), T}(newmo, p.co)
end


#.. AA/Singular interoperability

abstractalgebra(ctx :: PolynomialΓ) = AA.PolynomialRing(abstractalgebra(ctx.co), variables(ctx))

function (ctx :: MonomialΓ)(m ::AA.MPolyElem)
    exp = first(exponent_vectors(m))
    ctx(Monomial{nvars(ctx), exponenttype(ctx)}(exp))
end

function (ctx :: PolynomialΓ)(p :: AA.MPolyElem)
    mo = [ctx.mo(m) for m in AA.monomials(p)]
    if typeof(p) <: Singular.spoly
        co = [ctx.co(Int(c)) for c in Singular.coefficients(p)]
    else
        co = [ctx.co(AA.coeff(p, i)) for i in 1:length(p)]
    end
    p = ctx(mo, co)
    sort!(p, rev=true, order=order(ctx))
    return p
end

function (R :: AA.MPolyRing)(ctx, p :: Polynomial)
    br = AA.base_ring(R)
    if typeof(R) <: Singular.PolyRing
        C = MPolyBuildCtx(R)
        for (m, c) in p
            push_term!(C, br(Int(c)), Vector{Int}(exponents(ctx.mo, m)))
        end
        finish(C)
    else    
        return R([br(coefficient(p, i)) for i in 1:length(p)],
                 [convert(Vector{Int}, exponents(ctx.mo, monomial(p, i))) for i in 1:length(p)])
    end
end

