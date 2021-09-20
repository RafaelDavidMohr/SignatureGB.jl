const Data{M, T} = NamedTuple{(:poly, :sigtail, :sigratio),
                              Tuple{Polynomial{M, T}, Polynomial{M, T}, M}}
const SigTable{I, M, T} = SlicedDict{I, M, Data{M, T}}

mutable struct SigPolynomialΓ{I, M, T, MΓ<:Context{M}, TΓ<:Context{T}}<:Context{Tuple{I, M}}
    po::PolynomialΓ{M, T, MΓ, TΓ}
    tbl::SigTable{I, M, T}
end

pos_type(::SigPolynomialΓ{I}) where I = I
mon_type(::SigPolynomialΓ{I, M}) where {I, M} = M
coeff_type(::SigPolynomialΓ{I, M, T}) where {I, M, T} = T

function idxsigpolynomialctx(coefficients;
                             monomials=nothing,
                             index_type=UInt32,
                             mask_type=UInt32,
                             pos_type=UInt32,
                             kwargs...)
    if isnothing(monomials)
        moctx = ixmonomialctx(; indices=index_type, mask_type=mask_type, kwargs...)
    end
    po = polynomialctx(coefficients, monomials = moctx)
    tbl = emptysldict(pos_type, eltype(moctx), Data{eltype(moctx), eltype(coefficients)})
    SigPolynomialΓ{pos_type, eltype(moctx), eltype(coefficients),
                   typeof(moctx), typeof(coefficients)}(po, tbl)
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

# get functions

function (ctx::SigPolynomialΓ{I, M})(sig::Tuple{I, M}) where {I, M, MO}
    get(ctx.tbl, sig) do
        error("Nothing registered under the signature $(sign)")
    end
end

function (ctx::SigPolynomialΓ{I, M, T})(m::M, sig::Tuple{I, M}) where {I, M, T}
    @assert sig in keys(ctx.tbl)
    key = (sig[1], mul(ctx.po.mo, m, sig[2]))
    get(ctx.tbl, key) do
        val = ctx.tbl[sig]
        Data{M, T}((mul(ctx.po, val[:poly], m), mul(ctx.po, val[:sigtail], m), val[:sigratio]))
    end
end

# forwarding of functions on polynomials

leadingmonomial(ctx::SigPolynomialΓ{I, M}, sig::Tuple{I, M}) where {I, M} = leadingmonomial(ctx(sig)[:poly])

# sorting

@inline @generated function lt(ctx::SigPolynomialΓ{I, M},
                               a::Tuple{I, M},
                               b::Tuple{I, M},
                               ::Val{S}) where {I, M, S}

    if S == :POT
        quote
            if a[1] == b[1]
                return lt(ctx.po.mo, a[2], b[2])
            end
            return a[1] < b[1]
        end
    elseif S == :TOP
        quote
            if a[2] == b[2]
                return a[1] < b[1]
            end
            return lt(ctx.po.mo, a[2], b[2])
        end
    end
end

# Abstract Algebra

(ctx::SigPolynomialΓ)(i, m::AA.MPolyElem) = (pos_type(ctx)(i), ctx.po.mo(m))
(ctx::SigPolynomialΓ{I, M})(sig::Tuple{I, M}, p::AA.MPolyElem) where {I, M} = ctx(sig, ctx.po(p))
