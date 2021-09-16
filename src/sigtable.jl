const Data{M, T} = NamedTuple{(:poly, :sigtail), Tuple{Polynomial{M, T}, Polynomial{M, T}}}
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
                             indices=UInt32,
                             mask_type=UInt32,
                             pos_type=UInt32,
                             kwargs...)
    if isnothing(monomials)
        moctx = ixmonomialctx(; indices=indices, mask_type=mask_type, kwargs...)
        println(typeof(moctx))
    end
    po = polynomialctx(coefficients, monomials = moctx)
    tbl = emptysldict(pos_type, eltype(moctx), Data{eltype(moctx), eltype(coefficients)})
    SigPolynomialΓ{pos_type, eltype(moctx), eltype(coefficients),
                   typeof(moctx), typeof(coefficients)}(po, tbl)
end

function (ctx::SigPolynomialΓ{I, M, T})(sig::Tuple{I, M},
                                        pol::Polynomial{M, T},
                                        sigtail::Polynomial{M, T}) where {I, M, T}
    val = Data{M, T}((pol, sigtail))
    try
        ctx.tbl[sig] = val
    catch
        insert!(ctx.tbl, sig, val)
    end
end

(ctx::SigPolynomialΓ{I, M, T})(sig::Tuple{I, M}, pol::Polynomial{M, T}) where {I, M, T} = ctx(sig, pol, zero(pol))

function (ctx::SigPolynomialΓ{I, M, T})(m::M, sig::Tuple{I, M}) where {I, M, T}
    @assert sig in keys(ctx.tbl)
    key = (sig[1], mul(ctx.po.mo, m, sig[2]))
    get(ctx.tbl, key) do
        val = ctx.tbl[sig]
        Data{M, T}((mul(ctx.po, val[:poly], m), mul(ctx.po, val[:sigtail], m)))
    end
end

# Abstract Algebra

(ctx::SigPolynomialΓ{I, M})(sig::Tuple{I, M}, p::AA.MPolyElem) where {I, M} = ctx(sig, ctx.po(p))
