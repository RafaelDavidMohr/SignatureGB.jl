function interreduce(ctx::SigPolynomialΓ{I, M},
                     G::Basis{I, M},
                     H::Syz{I, M}) where {I, M}

    unit = Base.one(ctx.po.mo)
    to_reduce = Set([(unit, (i, g)) for (i, Gi) in G for (g, lm) in Gi])

    mons = symbolic_pp!(ctx, to_reduce, G, H, are_pairs = false, interreduction_step = true)
    interred_mat = f5matrix(ctx, mons, collect(to_reduce), interreduction_step = true)
    full_reduction!(ctx, interred_mat)
    
    G_new = new_basis(ctx, length(G))
    for (sig, row) in zip(interred_mat.sigs, interred_mat.rows)
        (m, (pos_key, t)) = sig
        m != unit && continue
        isempty(row) && continue
        p = unindexpolynomial(interred_mat.tbl, row)
        ctx(sig[2], p)
        push!(G_new[pos_key], (t, leadingmonomial(p)))
    end
    G_new
end

function full_reduction!(ctx, mat::F5matrix)

    sigs_and_rows = sort(collect(zip(mat.sigs, mat.rows)),
                         lt = (a, b) -> lt_full_red(ctx, a, b))
    mat.sigs = map(x -> x[1], sigs_and_rows)
    mat.rows = map(x -> x[2], sigs_and_rows)
    reduction!(mat)
end

function lt_full_red(ctx::SigPolynomialΓ{I, M},
                     sig_and_rw_1::Tuple{MonSigPair{I, M}, Polynomial{J, T}},
                     sig_and_rw_2::Tuple{MonSigPair{I, M}, Polynomial{J, T}}) where {I, M, J, T}

    unit = Base.one(ctx.po.mo)
    g1, g2 = sig_and_rw_1[1], sig_and_rw_2[1]
    g1[1] == unit && g2[1] != unit && return false
    g1[1] != unit && g2[1] == unit && return true
    p1, p2 = sig_and_rw_1[2], sig_and_rw_2[2]
    leadingmonomial(p1) > leadingmonomial(p2)
end
