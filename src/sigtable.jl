const Data{M, T} = NamedTuple{(:poly, :sigtail, :sigratio),
                              Tuple{Polynomial{M, T}, Polynomial{M, T}, M}}
const SigTable{I, M, T} = Dict{Tuple{I, M}, Data{M, T}}

mutable struct SigPolynomialΓ{I, M, T, MΓ<:Context{M}, TΓ<:Context{T}, PΓ<:PolynomialΓ{M, T, MΓ, TΓ}, S}<:Context{Tuple{I, M}}
    po::PΓ
    tbl::SigTable{I, M, T}
    ord_indices::Dict{I, I}
end

pos_type(::SigPolynomialΓ{I}) where {I} = I
mon_type(::SigPolynomialΓ{I, M}) where {I, M} = M
coeff_type(::SigPolynomialΓ{I, M, T}) where {I, M, T} = T
mod_order(::SigPolynomialΓ{I, M, T, MΓ, TΓ, PΓ, S}) where {I, M, T, MΓ, TΓ, PΓ, S} = S

function idxsigpolynomialctx(coefficients,
                             ngens;
                             monomials=nothing,
                             index_type=UInt32,
                             mask_type=UInt32,
                             pos_type=UInt32,
                             mod_order=:POT,
                             deg_bound = 0,
                             kwargs...)
    if isnothing(monomials)
        moctx = ixmonomialctx(; indices=index_type, mask_type=mask_type, deg_bound=deg_bound, kwargs...)
    end
    po = polynomialctx(coefficients, monomials = moctx)
    tbl = SigTable{pos_type, index_type, eltype(coefficients)}()
    ord_indices = Dict([(pos_type(i), pos_type(i)) for i in 1:ngens])
    SigPolynomialΓ{pos_type, eltype(moctx), eltype(coefficients),
                   typeof(moctx), typeof(coefficients), typeof(po), mod_order}(po, tbl, ord_indices)
end

# registration functions

function (ctx::SigPolynomialΓ{I, M, T})(sig::Tuple{I, M},
                                        pol::Polynomial{M, T},
                                        sigtail::Polynomial{M, T}) where {I, MO, M, T}
    if iszero(pol)
        ratio = one(ctx.po.mo)
    else
        ratio = div(ctx.po.mo, sig[2], leadingmonomial(pol))
    end
    val = Data{M, T}((pol, sigtail, ratio))
    try
        ctx.tbl[sig] = val
    catch
        insert!(ctx.tbl, sig, val)
    end
end

(ctx::SigPolynomialΓ{I, M, T})(sig::Tuple{I, M}, pol::Polynomial{M, T}) where {I, M, T} = ctx(sig, pol, zero(pol))

Base.getindex(ctx::SigPolynomialΓ{I, M}, sig::Tuple{I, M}) where {I, M} = getindex(ctx.tbl, sig)

# get functions

# WARNING: if sig::Tuple{J, MO} where J != I or MO != M then this will convert sig to a Tuple{I, M}

@inline function (ctx::SigPolynomialΓ{I, M})(sig::Tuple{I, M}) where {I, M, MO}
    ctx.tbl[sig]
    # get(ctx.tbl, sig) do
    #     error("Nothing registered under the signature $(sign)")
    # end
end

function (ctx::SigPolynomialΓ{I, M, T})(m::M, sig::Tuple{I, M}; orig_elem = true) where {I, M, T}
    @assert sig in keys(ctx.tbl)
    key = (sig[1], mul(ctx.po.mo, m, sig[2]))
    if !(orig_elem)
        get(ctx.tbl, key) do
            val = ctx.tbl[sig]
            Data{M, T}((mul(ctx.po, val[:poly], m), mul(ctx.po, val[:sigtail], m), val[:sigratio]))
        end
    end
    val = ctx.tbl[sig]
    Data{M, T}((mul(ctx.po, val[:poly], m), mul(ctx.po, val[:sigtail], m), val[:sigratio]))
end

# forwarding of functions on polynomials/monomials

function mul(ctx::SigPolynomialΓ{I, M}, m::M, sig::Tuple{I, M}) where {I, M}
    (sig[1], mul(ctx.po.mo, m, sig[2]))
end

function divides(ctx::SigPolynomialΓ{I, M}, s1::Tuple{I, M}, s2::Tuple{I, M}) where {I, M}
    s1[1] == s2[1] && divides(ctx.po.mo, s1[2], s2[2])
end

@inline leadingmonomial(ctx::SigPolynomialΓ{I, M}, sig::Tuple{I, M}) where {I, M} = leadingmonomial(ctx(sig)[:poly])

# sorting

@inline @generated function lt(ctx::SigPolynomialΓ{I, M, T, MΓ, TΓ, PΓ, S},
                               a::Tuple{I, M},
                               b::Tuple{I, M}) where {I, M, T, MΓ, TΓ, PΓ, S}

    if S == :POT
        quote
            if a[1] == b[1]
                return lt(ctx.po.mo, a[2], b[2])
            end
            return ctx.ord_indices[a[1]] < ctx.ord_indices[b[1]]
        end
    elseif S == :TOP
        quote
            if a[2] == b[2]
                return ctx.ord_indices[a[1]] < ctx.ord_indices[b[1]]
            end
            return lt(ctx.po.mo, a[2], b[2])
        end
    end
end

# Abstract Algebra

(ctx::SigPolynomialΓ)(i, m::AA.MPolyElem) = (pos_type(ctx)(i), ctx.po.mo(m))
(ctx::SigPolynomialΓ{I, M})(sig::Tuple{I, M}, p::AA.MPolyElem) where {I, M} = ctx(sig, ctx.po(p))

function (R :: AA.MPolyRing)(ctx::SigPolynomialΓ{I, M},
                             sig::Tuple{I, M}) where {I, M}

    R(ctx.po, ctx(sig)[:poly])
end
