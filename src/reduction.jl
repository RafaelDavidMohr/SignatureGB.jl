using Combinatorics

mutable struct F5matrix{I, M, T, J,
                        SΓ <: SigPolynomialΓ{I, M, T},
                        O <: Base.Order.Ordering}
    sigs_rows::SortedDict{MonSigPair{I, M}, Polynomial{J, T}, O}
    tbl::EasyTable{M, J}
    ctx::SΓ
    max_pos::I
end

function f5matrix(ctx::SigPolynomialΓ{I, M, T},
                  mons::Vector{M},
                  row_sigs::Vector{MonSigPair{I, M}};
                  enable_lower_pos_rewrite = true,
                  interreduction_step = false) where {I, M, T}

    max_pos = maximum(p -> pos(p), row_sigs)
    get_orig_elem = p -> interreduction_step || (!(enable_lower_pos_rewrite) && pos(p) < max_pos)
    tbl = easytable(mons)
    rows = Array{Polynomial{ind_type(tbl), T}}(undef, length(row_sigs))
    pols = [ctx(p..., orig_elem = get_orig_elem(p))[:poly]
            for p in row_sigs]
    @inbounds begin
        for (i, sig) in enumerate(row_sigs)
            rows[i] = indexpolynomial(tbl, pols[i])
        end
    end

    if interreduction_step
        sigs_lms = Dict(zip(row_sigs, [leadingmonomial(row) for row in rows]))
        row_order = interredorder(ctx, sigs_lms)
    else
        row_order = mpairordering(ctx)
    end
    
    sigs_rows = SortedDict(zip(row_sigs, rows), row_order)
    F5matrix(sigs_rows, tbl, ctx, max_pos)
end

rows(mat::F5matrix) = values(mat.sigs_rows)
sigs(mat::F5matrix) = keys(mat.sigs_rows)

function check_row_echelon(mat::F5matrix)
    for (p1, p2) in combinations(rows(mat), 2)
        (isempty(p1) || isempty(p2)) && continue
        leadingmonomial(p1) == leadingmonomial(p2) && return false
    end
    return true
end

# for printing matrices
function mat_show(mat::F5matrix)
    mat_vis = zeros(Int, length(rows(mat)), length(mat.tbl.val))
    for (i, row) in enumerate(rows(mat))
        for (j, c) in row
            mat_vis[i, j] = Int(c)
        end
    end
    mat_vis
end

Base.show(io::IO, mat::F5matrix) = Base.show(io, mat_show(mat))

function reduction!(mat::F5matrix{I, M, T, J}) where {I, M, T, J}
    n_cols = length(mat.tbl)
    pivots = repeat([nullmonsigpair(mat.ctx)], n_cols)
    Tbuf = buf_type(mat.ctx.po.co)
    buffer = zeros(Tbuf, n_cols)
    arit_operations = 0

    @inbounds begin
        for (i, (sig, row)) in enumerate(mat.sigs_rows)
            l = leadingmonomial(row)
            if isnull(mat.ctx, pivots[l])
                monic!(mat.ctx.po.co, row)
                pivots[l] = sig
                continue
            end
            buffer!(row, buffer)
            for (k, c) in enumerate(buffer)
                (iszero(c) || isnull(mat.ctx, pivots[k])) && continue
                arit_operations += length(mat.sigs_rows[pivots[k]])
                critical_loop!(buffer, mat.sigs_rows[pivots[k]], mat.ctx.po.co)
            end
            first_nz, new_row = unbuffer!(buffer, mat.ctx.po.co, J)
            if !(iszero(first_nz))
                pivots[first_nz] = sig
            end
            mat.sigs_rows[sig] = new_row
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
    end
end

# rows that need to be added

function new_elems_f5!(ctx::SΓ,
                       mat::F5matrix{I, M, T},
                       pairs::PairSet{I, M, SΓ},
                       G::Basis{I, M},
                       H::Syz{I, M};
                       enable_lower_pos_rewrite = true) where {I, M, T, SΓ <: SigPolynomialΓ{I, M, T}}
    
    @inbounds begin
        for (sig, row) in mat.sigs_rows
            m, (pos, t) = sig
            !(enable_lower_pos_rewrite) && pos < mat.max_pos && continue
            new_sig = mul(ctx, sig...)         
            if isempty(row)
                push!(H[pos], new_sig[2])
                new_rewriter!(ctx, pairs, new_sig)
            else
                p = unindexpolynomial(mat.tbl, row)
                # add element to basis if any of the following two conditions hold:
                # reductions of initial generators are added
                add_cond_1 = isone(ctx.po.mo[m]) && isone(ctx.po.mo[t]) && isempty(G[pos])
                # leading term dropped during reduction
                add_cond_2 = lt(ctx.po.mo, leadingmonomial(p), mul(ctx.po.mo, m, leadingmonomial(ctx((pos, t))[:poly])))
                if add_cond_1 || add_cond_2                    
                    ctx(new_sig, p)
                    lm = leadingmonomial(p)
                    new_rewriter!(ctx, pairs, new_sig)
                    push!(G[pos], (new_sig[2], lm))
                    pairs!(ctx, pairs, new_sig, lm, G, H, enable_lower_pos_rewrite = enable_lower_pos_rewrite)
                end
            end
        end
    end
end
