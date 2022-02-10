# TODO: is this needed?
mutable struct F5Data{I, SΓ<:SigPolynomialΓ{I}}
    ctx::SΓ
    R # singular ring
    trace_sig_tail_tags::Vector{Symbol}
    remasks_left::Int
end

function f5data(I::Vector{P};
                mod_order=:POT,
                trace_sig_tail_tags=Symbol[],
                index_type=UInt32,
                mask_type=UInt32,
                pos_type=UInt32,
                max_remasks=3,
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
    F5Data{pos_type, typeof(ctx)}(ctx, R, trace_sig_tail_tags, max_remasks)
end
