# UNFINISHED
using Combinatorics
using Lazy

abstract type MacaulayMatrix{K, J, T} end

function reduction!(mat::MacaulayMatrix)

    @debug "reducing matrix..."
    pivots = new_pivots(mat)
    buffer = new_buffer(mat)
    
    for (i, row) in enumerate(rows(mat))
        if ignore(mat, row, pivots)
            pivots[leadingmonomial(row)] = key
            continue
        end

        buffer!(row, buffer)
        for (k, c) in enumerate(buffer)
            (iszero(c) || isnull(pivots[k])) && continue
            critical_loop!(buffer, rows(mat)[pivots[k]], coeff_ctx(mat))
        end

        first_non_zero, new_row = unbuffer!(buffer, coeff_ctx(mat), ind_type(tbl(mat)))
        
        if !(iszero(first_non_zero))
            pivots[first_non_zero] = i
        end

        set_row!(mat, i, new_row)
    end
end

function mat_show(mat::MacaulayMatrix)
    mat_vis = zeros(Int, length(rows(mat)), length(tbl(mat)))
    for (i, (sig, row)) in enumerate(rows(mat))
        for (j, c) in row
            mat_vis[i, j] = Int(c)
        end
    end
    mat_vis
end

# base f5 matrix, no module representation
mutable struct F5matrix{I, M, J, T, O} <: MacaulayMatrix{MonSigPair{I, M}, J, T}
    sigs::Vector{MonSigPair{I, M}}
    rows::Vector{Polynomial{J, T}}
    tbl::EasyTable{M, J}
    ctx::SigPolynomialΓ{I, M, T}
end

function index_pols(mons::Vector{M},
                    sig_pols::Array{Tuple{MonSigPair{I, M}, Polynomial{M, T}}}) where {I, M, T}

    tbl = easytable(mons)
    sig_pols_indexed = [(sig, indexpolynomial(tbl, pol)) for (sig, pol) in sig_pols]
    return tbl, sig_pols_indexed
end
        
function f5_matrix(ctx::SigPolynomialΓ{I, M, MM, T},
                   tbl::EasyTable{M, J},
                   rows::Vector{Tuple{MonSigPair{I, M}, Polynomial{M, T}}}) where {I, M, MM, T, J}

    sort_mon_table!(tbl, ctx.po.mo)
    sigs = MonSigPair{I, M}[]
    mat_rows = Polynomial{J, T}[]
    sizehint!(sigs, length(rows))
    sizehint!(mat_rows, length(rows))
    for (sig, pol) in rows
        push!(sigs, sig)
        push!(mat_rows, indexpolynomial(tbl, pol))
    end
    F5matrix(sigs, mat_rows, data.tbl, ctx)
end

function is_triangular(mat::F5matrix)
    for (sig1, sig2) in combinations(collect(keys(mat.rows)), 2)
        (isempty(mat.rows[sig1]) || isempty(mat.rows[sig2])) && continue
        leadingmonomial(mat.rows[sig1]) == leadingmonomial(mat.rows[sig2]) && return false
    end
    return true
end

tbl(mat::F5matrix) = mat.tbl
rows(mat::F5matrix) = mat.rows
coeff_ctx(mat::F5matrix) = mat.ctx.po.co
pol(mat::F5matrix, row) = row
function new_pivots(mat::F5matrix)

    n_cols = length(mat.tbl)
    collect(Base.Iterators.repeated(0, n_cols))
end
function new_buffer(mat::F5matrix)

    n_cols = length(mat.tbl)
    zeros(buftype(coeff_ctx(mat)), n_cols)
end
function ignore(mat::F5matrix{I, M, J, T},
                row::Polynomial{J, T},
                pivots::Vector{MonSigPair{I, M}}) where {I, M, J, T}

    l = leadingmonomial(row)
    isnull(pivots[l])
end
function set_row!(mat::F5matrix{I, M, J, T},
                  i,
                  new_row::Polynomial{J, T}) where {I, M, J, T}

    mat.rows[i] = new_row
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
    
    mult1 = deflate(ctx, normal(ctx, buffer[leadingmonomial(pivot)]))
    mult2 = inv(ctx, coefficient(pivot, 1))
    mult = mul(ctx, mult1, mult2)
    sub_row!(buffer, pivot, mult, ctx)
    return mult
end

# # f5 matrices with tracking of module representation
# # TODO: assert pot module order in constructor
# mutable struct F5matrixPartialModule{I, M, J, T, O} <: MacaulayMatrix{MonSigPair{I, M}, J, T}
#     matrix::F5matrix{I, M, J, T, O}
#     module_matrix::F5matrix{I, M, J, T, O}
# end

# @forward F5matrixPartialModule.matrix tbl, coeff_ctx, new_pivots, ignore
# pol(mat::F5matrixPartialModule, row) = row[1]
# module_pol(mat::F5matrixPartialModule, sig) = rows(mat.module_matrix)[sig]
# function rows(mat::F5matrixPartialModule)
#     row_order = mpairordering(mat.matrix.ctx)
#     SortedDict(zip(keys(rows(mat.matrix)),
#                    zip(values(rows(mat.matrix)), values(rows(mat.module_matrix)))), row_order)
# end

# new_buffer(mat::F5matrixPartialModule) = (new_buffer(mat.matrix), new_buffer(mat.module_matrix))
# function set_row!(mat::F5matrixPartialModule{I, M, J, T},
#                   sig::MonSigPair{I, M},
#                   new_row::Tuple{Polynomial{J, T}, Polynomial{J, T}}) where {I, M, J, T}
#     set_row!(mat.matrix, sig, new_row[1])
#     set_row!(mat.module_matrix, sig, new_row[2])
# end

# function buffer!(row::Tuple{Polynomial{J, T}, Polynomial{J, T}},
#                  buffer::Tuple{Vector{Tbuf}, Vector{Tbuf}}) where {J, T, Tbuf}

#     buffer!(row[1], buffer[1])
#     buffer!(row[2], buffer[2])
# end

# function unbuffer!(buffer::Tuple{Vector{Tbuf}, Vector{Tbuf}},
#                    ctx::NmodLikeΓ{T, Tbuf},
#                    ::Type{J}) where {J, T, Tbuf}

#     first_nz, row_main = unbuffer!(buffer[1], ctx, J)
#     _, row_module = unbuffer!(buffer[2], ctx, J)
#     first_nz, (row_main, row_module)
# end

# function critical_loop!(buffer::Tuple{Vector{Tbuf}, Vector{Tbuf}},
#                         pivot::Tuple{Polynomial{J, T}, Polynomial{J, T}},
#                         ctx::NmodLikeΓ{T, Tbuf}) where {J, T, Tbuf}

#     mult = critical_loop!(buffer[1], pivot[1], ctx)
#     sub_row!(buffer[2], pivot[2], mult, ctx)
# end

# Final constructor

# function F5matrix(ctx::SigPolynomialΓ{I, M, MM, T},
#                   mons::Vector{M},
#                   row_sigs::Vector{MonSigPair{I, M}},
#                   curr_indx::I;
#                   kwargs...) where {I, M, MM, T}

#     matrix = f5_matrix(ctx, mons, row_sigs, curr_indx; kwargs...)
#     isnothing(mod_rep_type(ctx)) && return matrix
#     module_matrix = f5_matrix(ctx, M[], row_sigs, curr_indx, used_for = mod_rep_type(ctx); kwargs...)
#     return F5matrixPartialModule(matrix, module_matrix)
# end
