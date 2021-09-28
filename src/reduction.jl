mutable struct F5matrix{I, M, T, J, Tbuf, NΓ <: NmodLikeΓ{T, Tbuf}}
    sigs::PairSet{I, M}
    rows::Vector{Polynomial{J, T}}
    tbl::EasyTable{M, J}
    ctx::NΓ
end

function f5matrix(ctx::SigPolynomialΓ{I, M, T},
                  mons::MS,
                  row_sigs::PairSet{I, M}) where {I, M, T, MS <: SortedSet{M}}

    tbl = easytable(mons)
    rows = Array{Polynomial{ind_type(tbl), T}}(undef, length(row_sigs))
    for (i, sig) in enumerate(row_sigs)
        @inbounds rows[i] = indexpolynomial(tbl, ctx(sig...)[:poly])
    end
    F5matrix(row_sigs, rows, tbl, ctx.po.co)
end

# for printing matrices
function mat_show(mat::F5matrix)
    mat_vis = zeros(Int, length(mat.rows), length(mat.tbl.val))
    for (i, row) in enumerate(mat.rows)
        for (j, c) in row
            mat_vis[i, j] = Int(c)
        end
    end
    mat_vis
end

Base.show(io::IO, mat::F5matrix) = Base.show(io, mat_show(mat))

function reduction!(mat::F5matrix{I, M, T, J, Tbuf}) where {I, M, T, J, Tbuf}
    n_cols = length(mat.tbl)
    pivots = zeros(J, n_cols)
    buffer = zeros(Tbuf, n_cols)

    @inbounds begin
        for (i, row) in enumerate(mat.rows)
            l = leadingmonomial(row)
            if iszero(pivots[l])
                pivots[l] = J(i)
                continue
            end
            buffer!(row, buffer)
            for (k, c) in enumerate(buffer)
                (iszero(c) || iszero(pivots[k])) && continue
                critical_loop!(buffer, mat.rows[pivots[k]], mat.ctx)
            end
            first_nz, new_row = unbuffer!(buffer, mat.ctx, J)
            if !(iszero(first_nz))
                pivots[first_nz] = J(i)
            end
            mat.rows[i] = new_row
        end
    end
end
                           

function buffer!(row::Polynomial{J, T},
                 buffer::Vector{Tbuf}) where {J, M, T, Tbuf}

    [buffer[j] = Tbuf(c) for (j, c) in row]
end

function unbuffer!(buffer::Vector{Tbuf},
                   ctx::NmodLikeΓ{T, Tbuf},
                   ::Type{J}) where {T, Tbuf, J}

    coeffs = T[]
    mons = J[]
    first_nz = 0
    for (j, c) in enumerate(buffer)
        mod_coeff = deflate(ctx, normal(ctx, c))
        iszero(mod_coeff) && continue
        if iszero(first_nz)
            first_nz = J(j)
        end
        push!(coeffs, mod_coeff)
        push!(mons, J(j))
        buffer[j] = zero(Tbuf)
    end
    row = Polynomial(mons, coeffs)
    monic!(ctx, row)
    first_nz, row
end
        
function critical_loop!(buffer::Vector{Tbuf},
                        pivot::Polynomial{J, T},
                        ctx::NmodLikeΓ{T, Tbuf}) where {J, T, Tbuf}

    mult = deflate(ctx, normal(ctx, buffer[monomial(pivot, 1)]))
    buffer[monomial(pivot, 1)] = zero(Tbuf)
    try
        for (j, c) in pivot[2:end]
            buffer[j] = submul(ctx, buffer[j], mult, c)
        end
    catch BoundsError
        return
    end
end

# rows that need to be added

function new_elems_f5!(ctx::SΓ,
                       mat::F5matrix{I, M, T},
                       pairs::PairSet{I, M, SΓ},
                       G::Basis{I, M},
                       H::Basis{I, M}) where {I, M, T, SΓ <: SigPolynomialΓ{I, M, T}}

    for (i, sig) in enumerate(mat.sigs)
        m, (pos, t) = sig
        new_sig = (pos, mul(ctx.po.mo, m, t))
        @inbounds begin
            if iszero(mat.rows[i])
                insert!(H, new_sig)
                new_rewriter!(ctx, pairs, new_sig)
            else
                p = unindexpolynomial(mat.tbl, mat.rows[i])
                # add element to basis
                # reductions of initial generators are added
                add_cond_1 = isone(ctx.po.mo[m]) && isone(ctx.po.mo[t]) && !(new_sig in G)
                # leading term dropped during reduction
                add_cond_2 = lt(ctx.po.mo, leadingmonomial(p), mul(ctx.po.mo, m, leadingmonomial(ctx, (pos, t))))
                if add_cond_1 || add_cond_2
                    ctx(new_sig, p)
                    new_rewriter!(ctx, pairs, new_sig)
                    pairs!(ctx, pairs, new_sig, G, H)
                    insert!(G, new_sig)
                end
            end
        end
    end
end
