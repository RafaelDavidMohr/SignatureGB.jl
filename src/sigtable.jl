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

# TODO: Important!!!! swap T and MM in all the methods
# TODO: Include additional field for which tags we want to track the module?
mutable struct SigPolynomialΓ{I, M, MM, T, MODT,
                              MΓ<:Context{M}, TΓ<:Context{T},
                              MMΓ<:Context{MM},
                              PΓ<:PolynomialΓ{M, T, MΓ, TΓ},
                              PPΓ<:PolynomialΓ{M, T, MMΓ, TΓ}, MORD}<:Context{SigHash{I, M}}
    po::PΓ
    mod_po::PPΓ
    tbl::SigTable{I, M, MM, T, MODT}
    f5_indices::Dict{I, F5Index{I}}
    cashed_sigs::Vector{SigHash{I, M}}
    track_module_tags::Vector{Symbol}
    lms::Dict{I, M}
end

struct SigOrdering{SΓ <: SigPolynomialΓ}<:Base.Order.Ordering
    ctx::SΓ
end

function sigpolynomialctx(coefficients,
                          ngens;
                          polynomials=nothing,
                          mod_polynomials=nothing,
                          pos_type=UInt16,
                          mod_rep_type=nothing,
                          mod_order=:POT,
                          track_module_tags=Symbol[],
                          kwargs...)
    # TODO: what does 'deg_bound' do?
    # here we need to possibly build a seperate module_moctx
    if isnothing(polynomials)
        polynomials = polynomialctx(coefficients; kwargs...)
    end
    monomials = polynomials.mo
    
    if !(isnothing(mod_polynomials))
        error("using a different type of monomials for the module is currently not supported.")
    else
        mod_polynomials = polynomials
        mod_monomials = monomials
    end

    eltpe = SigHash{pos_type, eltype(monomials)}
    mon_type = eltype(monomials)
    tbl = SigTable{pos_type, mon_type, mon_type, eltype(coefficients), mod_rep_type}()
    f5_indices = Dict([(i, F5Index(i, :f)) for i in one(pos_type):pos_type(ngens)])
    SigPolynomialΓ{pos_type, eltype(monomials),
                   eltype(monomials), eltype(coefficients),
                   mod_rep_type, typeof(monomials),
                   typeof(coefficients), typeof(monomials),
                   typeof(polynomials), typeof(mod_polynomials),
                   mod_order}(polynomials, mod_polynomials, tbl, f5_indices,
                              eltpe[], track_module_tags, Dict{pos_type, mon_type}())
end

function Base.Order.lt(order::SigOrdering{SΓ},
                       a::SigHash{I, M},
                       b::SigHash{I, M}) where {I, M, SΓ <: SigPolynomialΓ{I, M}}
    lt(order.ctx, a, b)
end
sigordering(ctx::SΓ) where SΓ = SigOrdering{SΓ}(ctx)

function Base.show(io::IO,
                   a::Γpair0{SigHash{I, M}, SX}) where {I, M, SX <: SigPolynomialΓ{I, M}}
    ctx = a.ctx
    sighash = a.dat
    print(io, (Int(index(ctx, sighash)),
               convert(Vector{Int}, exponents(ctx.po.mo, sighash[2]))))
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
function mod_order(ctx::SigPolynomialΓ{I, M, MM, T,
                                       MODT, MΓ, TΓ,
                                       MMΓ, PΓ, PPΓ, MORD}) where {I, M, MM, T, MODT, MΓ, TΓ, MMΓ, PΓ, PPΓ, MORD}
    MORD
end
unitvector(ctx::SigPolynomialΓ, i) = (pos_type(ctx)(i), one(ctx.po.mo))
isunitvector(ctx::SigPolynomialΓ{I, M}, a::SigHash{I, M}) where {I, M} = isone(a[2])

function index(ctx::SigPolynomialΓ{I},
               i) where {I}

    iszero(i) && return zero(I)
    ctx.f5_indices[i].index
end
tag(ctx::SigPolynomialΓ{I}, i::I) where {I} = ctx.f5_indices[i].tag

index(ctx::SigPolynomialΓ{I, M}, p::SigHash{I, M}) where {I, M} = index(ctx, p[1])
tag(ctx::SigPolynomialΓ{I, M}, p::SigHash{I, M}) where {I, M} = tag(ctx, p[1])

function new_index!(ctx::SigPolynomialΓ,
                    index_key,
                    ind,
                    tag = :f)

    for i in keys(ctx.f5_indices)
        if index(ctx, i) >= ind
            ctx.f5_indices[i].index += 1
        end
    end
    ctx.f5_indices[index_key] = F5Index(pos_type(ctx)(ind), tag)
end

function new_generator!(ctx::SigPolynomialΓ{I, M, MM, T},
                        index,
                        pol::Polynomial{M, T},
                        tag = :f) where {I, M, MM, T}

    if !(isempty(keys(ctx.f5_indices)))
        new_index_key = maximum(keys(ctx.f5_indices)) + 1
    else
        new_index_key = 1
    end
    new_index!(ctx, new_index_key, index, tag)
    sighash = unitvector(ctx, new_index_key)
    # TODO: take care of other module reps
    if mod_order(ctx) in [:SCHREY, :DPOT]
        ctx.lms[new_index_key] = leadingmonomial(pol)
    end
    ctx(sighash, pol)
    return new_index_key
end

function new_generator!(ctx::SigPolynomialΓ{I, M, MM, T},
                        pol::Polynomial{M, T},
                        tag = :f) where {I, M, MM, T}
    
    new_generator!(ctx, maxindex(ctx) + 1, pol, tag)
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

# registration functions
# TODO: generalize type signature
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

# TODO: look at this
function (ctx::SigPolynomialΓ{I, M})(m::M, sig::Tuple{I, M}; no_rewrite = false) where {I, M}
    
    key = mul(ctx, m, sig)
    if !(no_rewrite)
        get(ctx.tbl, key) do
            cashed_rewriters = filter(p -> lt(ctx, sig, p) && divides(ctx, p, key), ctx.cashed_sigs)
            if isempty(cashed_rewriters)
                val = ctx.tbl[sig]
                return SigPolynomial(ctx, mul(ctx.po, val.pol, m), mul(ctx.mod_po, val.module_rep, m), val.sigratio)
            else
                # TODO: no need to sort here
                sort!(cashed_rewriters, lt = (p1, p2) -> lt(ctx, p1, p2), rev = true)
                rewr = first(cashed_rewriters)
                @debug "cached rewriter $(gpair(ctx, rewr)) for $(((m, sig), ctx))"
                n = div(ctx.po.mo, key[2], rewr[2])
                val = ctx.tbl[rewr]
                return SigPolynomial(ctx, mul(ctx.po, val.pol, n), mul(ctx.mod_po, val.module_rep, n), val.sigratio)
            end
        end
    else
        val = ctx.tbl[sig]
        return SigPolynomial(ctx, mul(ctx.po, val.pol, m), mul(ctx.mod_po, val.module_rep, m), val.sigratio)
    end
end

# get projection to highest index

function project(ctx::SigPolynomialΓ{I, M, M, T, :highest_index},
                 m::M,
                 sig::SigHash{I, M};
                 kwargs...) where {I, M, T}
    val = ctx(m, sig; kwargs...)
    msig = mul(ctx, m, sig)
    Polynomial{M, T}(vcat(msig[2], val.module_rep.mo),
                     vcat(one(T), val.module_rep.co))
end

function project(ctx::SigPolynomialΓ{I, M, M, T, :highest_index},
                 sig::SigHash{I, M}) where {I, M, T}
    project(ctx, one(ctx.po.mo), sig)
end
    
# forwarding of functions on polynomials/monomials

function mul(ctx::SigPolynomialΓ{I, M}, m::M, sig::SigHash{I, M}) where {I, M}
    (sig[1], mul(ctx.po.mo, m, sig[2]))
end

function divides(ctx::SigPolynomialΓ{I, M}, s1::SigHash{I, M}, s2::SigHash{I, M}) where {I, M}
    s1[1] == s2[1] && divides(ctx.po.mo, s1[2], s2[2])
end

@inline leadingmonomial(ctx::SigPolynomialΓ{I, M}, sig::SigHash{I, M}) where {I, M} = leadingmonomial(ctx(sig).pol)

@inline leadingmonomial(ctx::SigPolynomialΓ{I, M}, m::M, sig::SigHash{I, M}; no_rewrite = false) where {I, M} = leadingmonomial(ctx(m, sig, no_rewrite = no_rewrite).pol)

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
    elseif MORD == :DPOT
        quote
            d1 = degree(ctx.po.mo, a[2]) + degree(ctx.po.mo, ctx.lms[a[1]])
            d2 = degree(ctx.po.mo, b[2]) + degree(ctx.po.mo, ctx.lms[b[1]])
            if d1 == d2
                if a[1] == b[1]
                    return lt(ctx.po.mo, a[2], b[2])
                end
                return index(ctx, a[1]) < index(ctx, b[1])
            end
            return d1 < d2
        end
    elseif MORD == :TOP
        quote
            if a[2] == b[2]
                return index(ctx, a[1]) < index(ctx, b[1])
            end
            return lt(ctx.po.mo, a[2], b[2])
        end
    elseif MORD == :SCHREY
        quote
            c1 = mul(ctx.po.mo, a[2], ctx.lms[a[1]])
            c2 = mul(ctx.po.mo, b[2], ctx.lms[b[1]])
            if c1 == c2
                return index(ctx, a[1]) < index(ctx, b[1])
            end
            return lt(ctx.po.mo, c1, c2)
        end
    end
end

# Abstract Algebra

(ctx::SigPolynomialΓ)(i, m::AA.MPolyElem) = (pos_type(ctx)(i), ctx.po.mo(m))
(ctx::SigPolynomialΓ{I, M})(sig::Tuple{I, M}, p::AA.MPolyElem) where {I, M} = ctx(sig, ctx.po(p))

function (R :: AA.MPolyRing)(ctx::SigPolynomialΓ{I, M},
                             sig::Tuple{I, M}) where {I, M}

    R(ctx.po, ctx(sig).pol)
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
    if !(mod_order in [:POT, :SCHREY, :DPOT])
        error("only position over term, degree position over term or schreyer order currently supported")
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
            println(Int(coeffs[i]))
            ctx(unitvector(ctx, i), ctx.po(f), Polynomial([one(ctx.mod_po.mo)], [coeffs[i]]))
        end
    end
    if mod_order == :SCHREY || mod_order == :DPOT
        ctx.lms = Dict([(pos_type(ctx)(i), leadingmonomial(ctx, unitvector(ctx, i)))
                        for i in 1:length(I)])
    end
    ctx
end
