# TODO: Maybe introduce a type parameter to have specialized methods for different kinds
# of module reps
struct SigPolynomial{M, MM, T, MODT}
    pol::Polynomial{M, T}
    module_rep::Polynomial{MM, T}
    sigratio::M
end
    
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
    f5_indices::Dict{I, F5Index{I}}
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
function mod_order(::SigPolynomialΓ{I, M, MM, T,
                                    MODT, MΓ, TΓ,
                                    MMΓ, PΓ, PPΓ, MORD}) where {I, M, MM, T, MODT, MΓ, TΓ, MMΓ, PΓ, PPΓ, MORD}
    MORD
end
unitvector(ctx::SigPolynomialΓ, i) = (pos_type(ctx)(i), one(ctx.po.mo))

function index(ctx::SigPolynomialΓ{I},
               i::I) where {I}

    iszero(i) && return zero(I)
    ctx.f5_indices[i].index
end
tag(ctx::SigPolynomialΓ{I}, i::I) where {I} = ctx.f5_indices[i].tag

index(ctx::SigPolynomialΓ{I, M}, p::SigHash{I, M}) where {I, M} = index(ctx, p[1])
tag(ctx::SigPolynomialΓ{I, M}, p::SigHash{I, M}) where {I, M} = tag(ctx, p[1])

function new_index!(ctx::SigPolynomialΓ{I},
                    index_key::I,
                    index::I,
                    tag = :f) where I

    for i in keys(ctx.f5_indices)
        if index(ctx, i) >= index
            ctx.f5_indices[i].index += one(I)
        end
    end
    ctx.f5_indices[index_key] = F5Index(index, tag)
end

function new_generator!(ctx::SigPolynomialΓ{I, M, MM, T},
                        index::I,
                        pol::Polynomial{M, T},
                        module_rep::Polynomial{MM, T},
                        tag = :f) where {I, M, MM, T}

    new_index_key = maximum(keys(ctx.f5_indices)) + one(I)
    new_index!(ctx, new_index_key, index, tag)
    sighash = unitvector(ctx, new_index_key)
    ctx(sighash, pol, module_rep)
end

# find maximal index
function maxindex(ctx::SigPolynomialΓ{I, M}) where {I, M}

    maximum(v -> v.index, values(ctx.f5_indices))
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

# TODO: rewrite this constructor
# I dont understand the 'monomials' kwarg
function idxsigpolynomialctx(coefficients,
                             ngens;
                             monomials=nothing,
                             mon_index_type=UInt32,
                             mask_type=UInt32,
                             pos_type=UInt32,
                             same_module_context=true,
                             mod_rep_type=:highest_index,
                             mod_order=:POT,
                             deg_bound = 0,
                             kwargs...)
    # TODO: what does 'deg_bound' do?
    if isnothing(monomials)
        moctx = ixmonomialctx(; indices=mon_index_type, mask_type=mask_type, deg_bound=deg_bound, kwargs...)
    end
    # here we need to possibly build a seperate module_moctx
    if !(same_module_context)
        error("using a different type of monomials for the module is currently not supported.")
    end
    po = polynomialctx(coefficients, monomials = moctx)
    tbl = SigTable{pos_type, mon_index_type, mon_index_type, eltype(coefficients), mod_rep_type}()
    f5_indices = Dict([(pos_type(i), F5Index(pos_type(i), :f)) for i in 1:ngens])
    SigPolynomialΓ{pos_type, eltype(moctx), eltype(moctx), eltype(coefficients),
                   mod_rep_type, typeof(moctx), typeof(coefficients), typeof(moctx),
                   typeof(po), typeof(po), mod_order}(po, po, tbl, f5_indices)
end

# registration functions

function (ctx::SigPolynomialΓ{I, M, MM, T})(sig::SigHash{I, M},
                                            pol::Polynomial{M, T},
                                            module_rep::Polynomial{MM, T}) where {I, M, MM, T}
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
            val = ctx.tbl[sig]
            SigPolynomial(ctx, mul(ctx.po, val.pol, m), mul(ctx.mod_po, val.module_rep, m), val.sigratio)
        end
    end
    val = ctx.tbl[sig]
    SigPolynomial(ctx, mul(ctx.po, val.pol, m), mul(ctx.mod_po, val.module_rep, m), val.sigratio)
end

# get projection to highest index

function project(ctx::SigPolynomialΓ{I, M, M, T, :highest_index},
                 sig::SigHash{I, M}) where {I, M, T}

    Polynomial{M, T}(vcat(sig[2], ctx[sig].module_rep.mo), vcat(one(T), ctx[sig].module_rep.co))
end

# forwarding of functions on polynomials/monomials

function mul(ctx::SigPolynomialΓ{I, M}, m::M, sig::SigHash{I, M}) where {I, M}
    (sig[1], mul(ctx.po.mo, m, sig[2]))
end

function divides(ctx::SigPolynomialΓ{I, M}, s1::SigHash{I, M}, s2::SigHash{I, M}) where {I, M}
    s1[1] == s2[1] && divides(ctx.po.mo, s1[2], s2[2])
end

@inline leadingmonomial(ctx::SigPolynomialΓ{I, M}, sig::SigHash{I, M}) where {I, M} = leadingmonomial(ctx(sig)[:poly])

@inline leadingmonomial(ctx::SigPolynomialΓ{I, M}, m::M, sig::SigHash{I, M}) where {I, M} = leadingmonomial(ctx(m, sig)[:poly])

# sorting
@inline @generated function lt(ctx::SigPolynomialΓ{I, M, MM, T, MODT, MΓ, MMΓ, TΓ, PΓ, PPΓ, MORD},
                               a::SigHash{I, M},
                               b::SigHash{I, M}) where {I, M, MM, T, MODT, MΓ, MMΓ, TΓ, PΓ, PPΓ, MORD}

    println(MORD)
    if MORD == :POT
        quote
            if a[1] == b[1]
                return lt(ctx.po.mo, a[2], b[2])
            end
            return index(ctx, a[1]) < index(ctx, b[1])
        end
    elseif MORD == :TOP
        quote
            if a[2] == b[2]
                return index(ctx, a[1]) < index(ctx, b[1])
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
