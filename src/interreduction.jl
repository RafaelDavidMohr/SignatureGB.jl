function interreduce(ctx::SigPolynomialΓ{I, M},
                     G::Basis{I, M},
                     H::Syz{I, M};
                     verbose = false) where {I, M}

    unit = Base.one(ctx.po.mo)
    to_reduce = Set([(unit, (i, g)) for (i, Gi) in G for (g, lm) in Gi])

    symbolic_pp_timed = @timed symbolic_pp!(ctx, to_reduce, G, H, are_pairs = false, interreduction_step = true)
    mons = symbolic_pp_timed.value
    interred_mat = f5matrix(ctx, mons, collect(to_reduce), interreduction_step = true)
    mat_size = (length(rows(interred_mat)), length(interred_mat.tbl))

    if verbose 
        println("symbolic pp for interreduction matrix took $(symbolic_pp_timed.time) seconds.")
        println("size of interreduction matrix: $(mat_size)")
        println("reducing...")
    end
        
    red = @timed reduction!(interred_mat, interreduction_step = true)
    red_time = red.time
    arit_operations_interreduction, _ = red.value

    if verbose
        println("reduction of interreduction matrix took $(red_time) seconds.")
    end
    
    G_new = new_basis(ctx, G)
    for (sig, row) in interred_mat.sigs_rows
        (m, (pos_key, t)) = sig
        m != unit && continue
        isempty(row) && continue
        p = unindexpolynomial(interred_mat.tbl, row)
        ctx(sig[2], p)
        push!(G_new[pos_key], (t, leadingmonomial(p)))
    end

    G_new, arit_operations_interreduction, mat_size
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
