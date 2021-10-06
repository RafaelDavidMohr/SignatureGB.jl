using Combinatorics

mutable struct F5matrix{I, M, T, J, Tbuf, NΓ <: NmodLikeΓ{T, Tbuf}}
    sigs::MonSigSet{I, M}
    rows::Vector{Polynomial{J, T}}
    tbl::EasyTable{M, J}
    ctx::NΓ
end

function f5matrix(ctx::SigPolynomialΓ{I, M, T},
                  mons::Vector{M},
                  row_sigs::MonSigSet{I, M}) where {I, M, T}

    tbl = easytable(mons)
    rows = Array{Polynomial{ind_type(tbl), T}}(undef, length(row_sigs))
    pols = [ctx(sig...)[:poly] for sig in row_sigs]
    for (i, sig) in enumerate(row_sigs)
        @inbounds rows[i] = indexpolynomial(tbl, ctx(sig...)[:poly])
    end
    F5matrix(row_sigs, rows, tbl, ctx.po.co)
end

function check_row_echelon(mat::F5matrix)
    for (p1, p2) in combinations(mat.rows, 2)
        (isempty(p1) || isempty(p2)) && continue
        leadingmonomial(p1) == leadingmonomial(p2) && return false
    end
    return true
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
    arit_operations = 0

    @inbounds begin
        for ((i, row), sig) in zip(enumerate(mat.rows), mat.sigs)
            l = leadingmonomial(row)
            if iszero(pivots[l])
                pivots[l] = J(i)
                continue
            end
            buffer!(row, buffer)
            for (k, c) in enumerate(buffer)
                (iszero(c) || iszero(pivots[k])) && continue
                arit_operations += length(mat.rows[pivots[k]])
                critical_loop!(buffer, mat.rows[pivots[k]], mat.ctx)
            end
            first_nz, new_row = unbuffer!(buffer, mat.ctx, J)
            if !(iszero(first_nz))
                pivots[first_nz] = J(i)
            end
            mat.rows[i] = new_row
        end
    end
    arit_operations
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
p    end
end

# rows that need to be added

function new_elems_f5!(ctx::SΓ,
                       mat::F5matrix{I, M, T},
                       pairs::PairSet{I, M, SΓ},
                       G::Basis{I, M},
                       H::Syz{I, M}) where {I, M, T, SΓ <: SigPolynomialΓ{I, M, T}}

    zero_red_stats = Tuple{Int, Int}[]
    curr_degree = Int(degree(ctx.po.mo, first(mat.tbl.val)))
    rewrite_checks_time = 0.0
    new_rewriter_time = 0.0
    for (i, sig) in enumerate(mat.sigs)
        m, (pos, t) = sig
        new_sig = mul(ctx, sig...)
        @inbounds begin
            if isempty(mat.rows[i])
                push!(zero_red_stats, (Int(pos), curr_degree))
                push!(H[pos], new_sig[2])
                new_rewriter!(ctx, pairs, new_sig)
            else
                p = unindexpolynomial(mat.tbl, mat.rows[i])
                # add element to basis if any of the following two conditions hold:
                # reductions of initial generators are added
                add_cond_1 = isone(ctx.po.mo[m]) && isone(ctx.po.mo[t]) && !(new_sig[2] in keys(G[pos]))
                # leading term dropped during reduction
                add_cond_2 = lt(ctx.po.mo, leadingmonomial(p), leadingmonomial(ctx(sig...)[:poly]))
                if add_cond_1 || add_cond_2
                    @debug "adding:" pretty_print(ctx, sig)
                    ctx(new_sig, p)
                    lm = leadingmonomial(p)
                    new_rewriter_time += @elapsed new_rewriter!(ctx, pairs, new_sig)
                    insert!(G[pos], new_sig[2], lm)
                    rewrite_checks_time += @elapsed pairs!(ctx, pairs, new_sig, lm, G, H)
                end
            end
        end
    end
    new_rewriter_time, rewrite_checks_time, zero_red_stats
end
