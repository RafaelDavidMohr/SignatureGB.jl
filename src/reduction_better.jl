# UNFINISHED
using Combinatorics
using Lazy

# Must implement
#  - rows
#  - new_pivots
#  - new_buffer
#  - ignore
#  - coeff_ctx
#  - set_row!
abstract type MacaulayMatrix{K, J, T} end

function reduction!(mat::MacaulayMatrix)

    pivots = new_pivots(mat)
    buffer = new_buffer(mat)
    
    for (key, row) in rows(mat)
        l = leadingmonomial(row)
        if ignore(mat, key, row, pivots)
            pivots[l] = key
            continue
        end

        buffer!(row, buffer)
        for (k, c) in enumerate(buffer)
            (iszero(c) || isnull(pivots[k])) && continue
            # TODO: record arit ops
            critical_loop!(buffer, rows(mat)[pivots[k]], coeff_ctx(mat))
        end

        first_non_zero, new_row = unbuffer!(buffer, coeff_ctx(mat))

        if !(iszero(first_non_zero))
            pivots[first_non_zero] = key
        end

        set_row!(mat, key, new_row)
    end
end

# base f5 matrix, no module representation
mutable struct F5matrix{I, M, J, T, O} <: MacaulayMatrix{MonSigPair{I, M}, J, T}
    rows::SortedDict{MonSigPair{I, M}, Polynomial{J, T}, O}
    tbl::EasyTable{M, J}
    ctx::SigPolynomialΓ{I, M, T}
    interreduction_matrix::Bool
end

rows(mat::F5matrix) = mat.rows
coeff_ctx(mat::F5matrix) = mat.ctx.po.co
function new_pivots(mat::F5matrix)

    n_cols = length(mat.tbl)
    collect(Base.Iterators.repeated(nullmonsigpair(ctx), n_cols))
end
function new_buffer(mat::F5matrix)

    n_cols = length(mat.tbl)
    zeros(buftype(coeff_ctx(mat)), n_cols)
end
function ignore(mat::F5matrix{I, M, J, T},
                sig::MonSigPair{I, M},
                row::Polynomial{J, T},
                pivots::Vector{MonSigPair{I, M}}) where {I, M, J, T}

    mat.interreduction_matrix && return sig[1] != one(mat.ctx.po.mo)
    l = leadingmonomial(row)
    isnull(pivots[l])
end
function set_row!(mat::F5matrix{I, M, J, T},
                  sig::MonSigPair{I, M},
                  new_row::Polynomial{J, T}) where {I, M, J, T}

    mat.rows[sig] = new_row
end

function critical_loop!(buffer::Vector{Tbuf},
                        pivot::Polynomial{J, T},
                        ctx::NmodLikeΓ{T, Tbuf}) where {J, T, Tbuf}
    
    mult1 = deflate(ctx, normal(ctx, buffer[monomial(pivot, 1)]))
    mult2 = inv(ctx, coefficient(pivot, 1))
    mult = mul(ctx, mult1, mult2)
    buffer[monomial(pivot, 1)] = zero(Tbuf)
    try
        for (j, c) in pivot[2:end]
            buffer[j] = submul(ctx, buffer[j], mult, c)
        end
        return mult
    catch BoundsError
        return mult
    end
end

# f5 matrices with tracking of module representation
# TODO: assert pot module order in constructor
mutable struct F5matrixPartialModule{I, M, J, T, O}
    matrix::F5matrix{I, M, J, T, O}
    module_matrix::F5matrix{I, M, J, T, O}
    max_index::I
end

@forward F5matrixPartialModule.matrix coeff_ctx, new_pivots, ignore
rows(mat::F5matrixPartialModule) = (rows(mat.matrix), rows(mat.module_matrix))
new_buffer(mat::F5matrixPartialModule) = (new_buffer(mat.matrix), new_buffer(mat.module_matrix))
function set_row!(mat::F5matrix{I, M, J, T},
                  sig::MonSigPair{I, M},
                  new_row::Tuple{Polynomial{J, T}, Polynomial{J, T}})
    set_row!(mat.matrix, sig, new_row[1])
    set_row!(mat.module_matrix, sig, new_row[2])
end

# critical_loop!(buffer, rows(mat)[pivots[k]], coeff_ctx(mat))
# first_non_zero, new_row = unbuffer!(buffer, coeff_ctx(mat))
