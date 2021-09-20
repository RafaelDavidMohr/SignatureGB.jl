mutable struct F5Data{I, SΓ<:SigPolynomialΓ{I}}
    ctx::SΓ
    ord_indices::Dict{I, I}
    mod_order::Symbol
    trace_sig_tails::Bool
end

function f5data(I::Vector{P};
                mod_order=:POT,
                trace_sig_tails=true,
                index_type=UInt32,
                mask_type=UInt32,
                pos_type=UInt32,
                kwargs...) where {P <: AA.MPolyElem}

    R = parent(first(I))
    char = AA.characteristic(R)
    coeffs = Nmod32Γ(char)
    ctx = idxsigpolynomialctx(coeffs, index_type=index_type,
                              mask_type=mask_type, pos_type=pos_type; kwargs...)

    ord_indices = Dict([(pos_type(i), pos_type(i)) for i in 1:length(I)])
    for (i, f) in enumerate(I)
        sig = ctx(i, R(1))
        ctx(sig, f)
    end
    F5Data{pos_type, typeof(ctx)}(ctx, ord_indices, mod_order, trace_sig_tails)
end

# method forwarding

function lt(F5::F5Data{I, SΓ},
            a::Tuple{I, M},
            b::Tuple{I, M}) where {I, M, SΓ <: SigPolynomialΓ{I, M}}

    a1, b1 = (F5.ord_indices[a[1]], a[2]), (F5.ord_indices[b[1]], b[2])
    lt(F5.ctx, a1, b1, Val(F5.mod_order))
end
