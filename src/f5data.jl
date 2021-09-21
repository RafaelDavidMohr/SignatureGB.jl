mutable struct F5Data{I, SΓ<:SigPolynomialΓ{I}}
    ctx::SΓ
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
    ctx = idxsigpolynomialctx(coeffs, length(I), index_type=index_type,
                              mask_type=mask_type, pos_type=pos_type; kwargs...)

    for (i, f) in enumerate(I)
        sig = ctx(i, R(1))
        ctx(sig, f)
    end
    F5Data{pos_type, typeof(ctx)}(ctx, trace_sig_tails)
end

# method forwarding
