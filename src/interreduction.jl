function interreduce(ctx::SigPolynomialΓ{I, M},
                     G::Basis{I, M},
                     H::Syz{I, M}) where {I, M}

    unit = Base.one(ctx.po.mo)
    to_reduce = Set([(unit, (i, g)) for (i, Gi) in G for (g, lm) in Gi])

    mons = symbolic_pp!(ctx, to_reduce, G, H, are_pairs = false, interreduction_step = true)
    interred_mat = f5matrix(ctx, mons, collect(to_reduce), interreduction_step = true)
    reduction!(interred_mat)
    
    G_new = new_basis(ctx, length(G))
    for (sig, row) in interred_mat.sigs_rows
        (m, (pos_key, t)) = sig
        m != unit && continue
        isempty(row) && continue
        p = unindexpolynomial(interred_mat.tbl, row)
        ctx(sig[2], p)
        push!(G_new[pos_key], (t, leadingmonomial(p)))
    end
    G_new
end

struct InterredOrder{I, M, J, T, SΓ <: SigPolynomialΓ}<:Base.Order.Ordering
    ctx::SΓ
    sigs_lms::Dict{MonSigPair{I, M}, J}
end
function interredorder(ctx::SigPolynomialΓ{I, M, T},
                       sigs_lms::Dict{MonSigPair{I, M}, J}) where {I, M, J, T}
    InterredOrder{I, M, J, T, typeof(ctx)}(ctx, sigs_lms)
end

function Base.Order.lt(ord::InterredOrder{I, M},
                       sig1::MonSigPair{I, M},
                       sig2::MonSigPair{I, M}) where {I, M}

    ctx = ord.ctx
    unit = Base.one(ctx.po.mo)
    sig1[1] == unit && sig2[1] != unit && return false
    sig1[1] != unit && sig2[1] == unit && return true
    ord.sigs_lms[sig1] > ord.sigs_lms[sig2]
end
