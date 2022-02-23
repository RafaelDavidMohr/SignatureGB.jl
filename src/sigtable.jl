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
function mod_rep_type(::SigPolynomialΓ{I, M, MM, T,
                                       MODT}) where {I, M, MM, T, MODT}
    MODT
end
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
function sigpolynomialctx(coefficients,
                          ngens;
                          polynomials=nothing,
                          mod_polynomials=nothing,
                          pos_type=UInt32,
                          mod_rep_type=nothing,
                          mod_order=:POT,
                          kwargs...)
    # TODO: what does 'deg_bound' do?
    # here we need to possibly build a seperate module_moctx
    if isnothing(polynomials)
        polynomials = polynomialctx(coefficients; kwargs...)
        monomials = polynomials.mo
    end

    if !(isnothing(mod_polynomials))
        error("using a different type of monomials for the module is currently not supported.")
    else
        mod_polynomials = polynomials
        mod_monomials = monomials
    end

    mon_type = eltype(monomials)
    tbl = SigTable{pos_type, mon_type, mon_type, eltype(coefficients), mod_rep_type}()
    f5_indices = Dict([(i, F5Index(i, :f)) for i in one(pos_type):pos_type(ngens)])
    SigPolynomialΓ{pos_type, eltype(monomials),
                   eltype(monomials), eltype(coefficients),
                   mod_rep_type, typeof(monomials),
                   typeof(coefficients), typeof(monomials),
                   typeof(polynomials), typeof(mod_polynomials),
                   mod_order}(polynomials, mod_polynomials, tbl, f5_indices)
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

# converting a vector of singular polynomials into our own data structures
# TODO: rework constructors
function setup(I::Vector{P};
               mod_order=:POT,
               mon_order=:GREVLEX,
               modulus=32,
               buffer=64,
               kwargs...) where {P <: AA.MPolyElem}

    R = parent(first(I))
    char = characteristic(R)
    if mon_order == :GREVLEX
        order = Grevlex(Singular.nvars(R))
    else
        error("only grevlex order currently supported")
    end
    if mod_order != :POT
        error("only position over term order currently supported")
    end
    if modulus != 32
        error("only 32 bit modulus currently supported")
    end
    if !(buffer in [64, 128])
        error("choose a buffer bitsize of either 64 or 128")
    end
    buffer == 64 ? coefficients = Nmod32Γ(char) : coefficients = Nmod32xΓ(char)
    ctx = sigpolynomialctx(coefficients, length(I); mod_order = mod_order,
                           order=order, kwargs...)
    if mod_rep_type(ctx) in [nothing, :highest_index]
        for (i, f) in enumerate(I)
            ctx(unitvector(ctx, i), f)
        end
    elseif mod_rep_type(ctx) == :random_lin_comb
        T = eltype(coefficients)
        coeffs = rand(zero(T):T(char - 1), length(I))
        for (i, f) in enumerate(I)
            ctx(unitvector(ctx, i), f, ctx.mod_po(coeffs[i]))
        end
    end
    ctx
end
