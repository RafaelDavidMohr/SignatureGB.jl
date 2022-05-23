# UNFINISHED
using Combinatorics
using Lazy

mutable struct F5matrix{I, M, MM, J, K, T}
    sigs::Vector{MonSigPair{I, M}}
    rows::Vector{Polynomial{J, T}}
    module_rows::Vector{Polynomial{K, T}}
    tbl::EasyTable{M, J}
    module_tbl::EasyTable{MM, K}
    ctx::SigPolynomialΓ{I, M, MM, T}
end

function reduction!(mat::F5matrix)

    @debug "reducing matrix..."
    n_cols = length(mat.tbl)
    n_cols_module = length(mat.module_tbl)
    pivots = collect(Base.Iterators.repeated(0, n_cols))
    buffer = zeros(buftype(mat.ctx.po.co), n_cols)
    module_buffer = zeros(buftype(mat.ctx.mod_po.co), n_cols_module)
    
    for (i, row) in enumerate(mat.rows)
        if iszero(pivots[leadingmonomial(row)])
            pivots[leadingmonomial(row)] = i
            continue
        end

        buffer!(row, buffer)
        buffer!(mat.module_rows[i], module_buffer)
        for (k, c) in enumerate(buffer)
            (iszero(c) || iszero(pivots[k])) && continue
            mult = critical_loop!(buffer, mat.rows[pivots[k]], mat.ctx.po.co)
            sub_row!(module_buffer, mat.module_rows[pivots[k]], mult, mat.ctx.po.co)
        end

        first_non_zero, new_row = unbuffer!(buffer, mat.ctx.po.co, ind_type(mat.tbl))
        _, new_module_row = unbuffer!(module_buffer, mat.ctx.po.co, ind_type(mat.module_tbl))
        
        if !(iszero(first_non_zero))
            pivots[first_non_zero] = i
            mult = inv(mat.ctx.po.co, first(new_row.co))
            new_row = mul_scalar(ctx.po, new_row, mult)
            new_module_row = mul_scalar(ctx.po, new_module_row, mult)
        end

        mat.rows[i] = new_row
        mat.module_rows[i] = new_module_row
    end
end

function mat_show(mat::F5matrix)
    mat_vis = zeros(Int, length(rows(mat)), length(tbl(mat)))
    for (i, (sig, row)) in enumerate(rows(mat))
        for (j, c) in row
            mat_vis[i, j] = Int(c)
        end
    end
    mat_vis
end
        
function f5_matrix(ctx::SigPolynomialΓ{I, M, MM, T},
                   tbl::EasyTable{M, J},
                   module_tbl::EasyTable{MM, K},
                   rows::Vector{Tuple{MonSigPair{I, M}, Polynomial{M, T}, Polynomial{MM, T}}}) where {I, M, MM, T, J, K}

    sort_mon_table!(tbl, ctx.po.mo)
    sigs = MonSigPair{I, M}[]
    mat_rows = Polynomial{J, T}[]
    mat_module_rows = Polynomial{K, T}[]
    rows = sort(unique(rows), by = x -> x[1], lt = (s1, s2) -> Base.lt(mpairordering(ctx), s1, s2))
    
    sizehint!(sigs, length(rows))
    sizehint!(mat_rows, length(rows))
    sizehint!(mat_module_rows, length(rows))
    for (sig, pol, module_pol) in rows
        push!(sigs, sig)
        push!(mat_rows, indexpolynomial(tbl, pol))
        push!(mat_module_rows, indexpolynomial(tbl, module_pol))
    end
    F5matrix(sigs, mat_rows, mat_module_rows, tbl, module_tbl, ctx)
end

function is_triangular(mat::F5matrix)
    for (sig1, sig2) in combinations(collect(keys(mat.rows)), 2)
        (isempty(mat.rows[sig1]) || isempty(mat.rows[sig2])) && continue
        leadingmonomial(mat.rows[sig1]) == leadingmonomial(mat.rows[sig2]) && return false
    end
    return true
end

function buffer!(row::Polynomial{J, T},
                 buffer::Vector{Tbuf}) where {J, T, Tbuf}

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
    end
    fill!(buffer, zero(Tbuf))
    row = Polynomial(mons, coeffs)
    first_nz, row
end

function sub_row!(buffer::Vector{Tbuf},
                  pivot::Polynomial{J, T},
                  mult::T,
                  ctx::NmodLikeΓ{T, Tbuf}) where {J, T, Tbuf}

    iszero(pivot) && return
    @logmsg Verbose2 "" arit_ops = length(pivot)
    for (j, c) in pivot
        buffer[j] = submul(ctx, buffer[j], mult, c)
    end
end

function critical_loop!(buffer::Vector{Tbuf},
                        pivot::Polynomial{J, T},
                        ctx::NmodLikeΓ{T, Tbuf}) where {J, T, Tbuf}
    
    mult = deflate(ctx, normal(ctx, buffer[leadingmonomial(pivot)]))
    sub_row!(buffer, pivot, mult, ctx)
    return mult
end
