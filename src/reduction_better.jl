# UNFINISHED
using Combinatorics
using Lazy

abstract type MacaulayMatrix{K, J, T} end

function reduction!(mat::MacaulayMatrix)

    @debug "reducing matrix..."
    pivots = new_pivots(mat)
    buffer = new_buffer(mat)

    rws = rows(mat)
    
    for (key, row) in rws
        l = leadingmonomial(pol(mat, row))
        if ignore(mat, key, pol(mat, row), pivots)
            pivots[l] = key
            continue
        end

        buffer!(row, buffer)
        for (k, c) in enumerate(pol(mat, buffer))
            (iszero(c) || isnull(pivots[k])) && continue
            critical_loop!(buffer, rws[pivots[k]], coeff_ctx(mat))
        end

        first_non_zero, new_row = unbuffer!(buffer, coeff_ctx(mat), ind_type(tbl(mat)))
        
        if !(iszero(first_non_zero))
            pivots[first_non_zero] = key
        end

        rws[key] = new_row
        set_row!(mat, key, new_row)
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
    rows::SortedDict{MonSigPair{I, M}, Polynomial{J, T}, O}
    tbl::EasyTable{M, J}
    ctx::SigPolynomialΓ{I, M, T}
    interreduction_matrix::Bool
end

function index_pols(mons::Vector{M},
                    sig_pols::Array{Tuple{MonSigPair{I, M}, Polynomial{M, T}}}) where {I, M, T}

    tbl = easytable(mons)
    sig_pols_indexed = [(sig, indexpolynomial(tbl, pol)) for (sig, pol) in sig_pols]
    return tbl, sig_pols_indexed
end
        
function F5matrix(ctx::SigPolynomialΓ{I, M, MM, T},
                  mons::Vector{M},
                  row_sigs::Vector{MonSigPair{I, M}};
                  interreduction_matrix = false,
                  # used if an interreduction occured: in this case signatures are still hashes
                  f5c = false,
                  # used for matrix in which we track the projections to the largest index
                  # in this case we ignore the projections of elements in lower index
                  used_for = :pols) where {I, M, MM, T}

    if used_for == :pols
        max_index = maximum(p -> index(ctx, p), row_sigs)
        get_pol = p -> ctx(p..., no_rewrite = f5c && index(ctx, p) < max_index).pol
    elseif used_for == :highest_index
        largest_index = maximum(p -> index(ctx, p), row_sigs)
        get_pol = p -> index(ctx, p) < largest_index || !(tag(ctx, p) in ctx.track_module_tags) ? zero(ctx.po) : project(ctx, p...)
    end
        
    if interreduction_matrix
        @assert no_rewrite_criterion == p -> true
    end
    pols = [get_pol(sig) for sig in row_sigs]
    sig_pols = collect(zip(row_sigs, pols))
    # TODO: this might be unstable
    if isempty(mons)
        mons = unique(vcat([monomials(p) for p in pols]...))
        sort!(mons, lt = (a, b) -> lt(ctx.mod_po.mo, a, b), rev = true)
    end
    tbl, sig_poly_indexed = index_pols(mons, sig_pols)
    if interreduction_matrix
        sigs_lms = Dict([(sig, leadingmonomial(pol)) for (sig, pol) in sig_poly_indexed])
        row_order = interredorder(ctx, sigs_lms)
    else
        row_order = mpairordering(ctx)
    end
    
    rows = SortedDict(sig_poly_indexed, row_order)
    F5matrix(rows, tbl, ctx, interreduction_matrix)
end

tbl(mat::F5matrix) = mat.tbl
rows(mat::F5matrix) = mat.rows
coeff_ctx(mat::F5matrix) = mat.ctx.po.co
pol(mat::F5matrix, row) = row
function new_pivots(mat::F5matrix)

    n_cols = length(mat.tbl)
    collect(Base.Iterators.repeated(nullmonsigpair(mat.ctx), n_cols))
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
        buffer[j] = zero(Tbuf)
    end
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

# f5 matrices with tracking of module representation
# TODO: assert pot module order in constructor
mutable struct F5matrixPartialModule{I, M, J, T, O} <: MacaulayMatrix{MonSigPair{I, M}, J, T}
    matrix::F5matrix{I, M, J, T, O}
    module_matrix::F5matrix{I, M, J, T, O}
end

function F5matrixHighestIndex(ctx::SigPolynomialΓ{I, M, MM, T},
                              mons::Vector{M},
                              row_sigs::Vector{MonSigPair{I, M}};
                              kwargs...) where {I, M, MM, T}
    
    matrix = F5matrix(ctx, mons, row_sigs; kwargs...)
    module_matrix = F5matrix(ctx, M[], row_sigs, used_for = :highest_index; kwargs...)    
    return F5matrixPartialModule(matrix, module_matrix)
end

@forward F5matrixPartialModule.matrix tbl, coeff_ctx, new_pivots, ignore
pol(mat::F5matrixPartialModule, row) = row[1]
module_pol(mat::F5matrixPartialModule, sig) = rows(mat.module_matrix)[sig]
function rows(mat::F5matrixPartialModule)
    row_order = mpairordering(mat.matrix.ctx)
    SortedDict(zip(keys(rows(mat.matrix)),
                   zip(values(rows(mat.matrix)), values(rows(mat.module_matrix)))), row_order)
end

new_buffer(mat::F5matrixPartialModule) = (new_buffer(mat.matrix), new_buffer(mat.module_matrix))
function set_row!(mat::F5matrixPartialModule{I, M, J, T},
                  sig::MonSigPair{I, M},
                  new_row::Tuple{Polynomial{J, T}, Polynomial{J, T}}) where {I, M, J, T}
    set_row!(mat.matrix, sig, new_row[1])
    set_row!(mat.module_matrix, sig, new_row[2])
end

function buffer!(row::Tuple{Polynomial{J, T}, Polynomial{J, T}},
                 buffer::Tuple{Vector{Tbuf}, Vector{Tbuf}}) where {J, T, Tbuf}

    buffer!(row[1], buffer[1])
    buffer!(row[2], buffer[2])
end

function unbuffer!(buffer::Tuple{Vector{Tbuf}, Vector{Tbuf}},
                   ctx::NmodLikeΓ{T, Tbuf},
                   ::Type{J}) where {J, T, Tbuf}

    first_nz, row_main = unbuffer!(buffer[1], ctx, J)
    _, row_module = unbuffer!(buffer[2], ctx, J)
    first_nz, (row_main, row_module)
end

function critical_loop!(buffer::Tuple{Vector{Tbuf}, Vector{Tbuf}},
                        pivot::Tuple{Polynomial{J, T}, Polynomial{J, T}},
                        ctx::NmodLikeΓ{T, Tbuf}) where {J, T, Tbuf}

    mult = critical_loop!(buffer[1], pivot[1], ctx)
    sub_row!(buffer[2], pivot[2], mult, ctx)
end
