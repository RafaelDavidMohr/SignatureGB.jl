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
                use_macaulay_bound=false,
                kwargs...) where {P <: AA.MPolyElem}

    R = parent(first(I))
    char = AA.characteristic(R)
    coeffs = Nmod32Γ(char)
    if use_macaulay_bound
        deg_bound = mac_bound(I)
    else
        deg_bound = 0
    end
    ctx = idxsigpolynomialctx(coeffs, length(I), index_type=index_type,
                              mask_type=mask_type, pos_type=pos_type,
                              deg_bound=deg_bound; kwargs...)

    for (i, f) in enumerate(I)
        sig = ctx(i, R(1))
        ctx(sig, f)
    end
    F5Data{pos_type, typeof(ctx)}(ctx, trace_sig_tails)
end

# method forwarding
