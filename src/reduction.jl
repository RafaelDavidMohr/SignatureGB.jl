using Combinatorics

mutable struct SimpleMatrix{I, M, T, J}
    rows::Dict{I, Polynomial{J, T}}
    tbl::EasyTable{M, J}
end

mutable struct F5matrix{I, M, T, J}
    sigs::Vector{MonSigPair{I, M}}
    sigtail_mat::SimpleMatrix{MonSigPair{I, M}, M, T, J}
    rows::Vector{Polynomial{J, T}}
    tbl::EasyTable{M, J}
    max_pos::I
end

function f5matrix(ctx::SigPolynomialΓ{I, M, T},
                  mons::Vector{M},
                  row_sigs::MonSigSet{I, M}) where {I, M, T}

    sigs = collect(row_sigs)
    max_pos = pos(ctx, last(row_sigs))
    tbl = easytable(mons)
    rows = Array{Polynomial{ind_type(tbl), T}}(undef, length(sigs))
    pols = [ctx(sig...)[:poly] for sig in sigs]
    for (i, sig) in enumerate(sigs)
        @inbounds rows[i] = indexpolynomial(tbl, ctx(sig...)[:poly])
    end

    # matrix to track the sigtails
    sigtails = [(sig, project(mul(ctx, sig...), ctx(sig...)[:sigtail])) for sig in sigs if pos(ctx, sig) == max_pos]
    sigtail_mons = sort(unique(vcat([s[2].mo for s in sigtails]...)), rev=true,
                        order = order(ctx.po.mo))
    sigtail_tbl = easytable(sigtail_mons)
    sigtail_mat = SimpleMatrix(Dict([(s[1], indexpolynomial(sigtail_tbl, s[2])) for s in sigtails]), sigtail_tbl)
    
    F5matrix(sigs, sigtail_mat, rows, tbl, max_pos)
end

function check_row_echelon(mat::F5matrix)
    for (p1, p2) in combinations(mat.rows, 2)
        (isempty(p1) || isempty(p2)) && continue
        leadingmonomial(p1) == leadingmonomial(p2) && return false
    end
    return true
end

# for printing matrices
function mat_show(mat)
    mat_vis = zeros(Int, length(mat.rows), length(mat.tbl.val))
    for (i, row) in enumerate(mat.rows)
        if typeof(mat) <: SimpleMatrix
            for (j, c) in row[2]
                mat_vis[i, j] = Int(c)
            end
        else
            for (j, c) in row
                mat_vis[i, j] = Int(c)
            end
        end
    end
    mat_vis
end

Base.show(io::IO, mat::F5matrix) = Base.show(io, mat_show(mat))

function reduction!(mat::F5matrix{I, M, T, J},
                    ctx::SigPolynomialΓ{I, M};
                    trace_sig_tails = false) where {I, M, T, J, Tbuf}
    n_cols = length(mat.tbl)
    pivots = zeros(J, n_cols)
    buffer = zeros(buftype(ctx.po.co), n_cols)
    sig_tail_buffer = copy(buffer)
    arit_operations = 0

    @inbounds begin
        for ((i, row), sig) in zip(enumerate(mat.rows), mat.sigs)
            should_add_sig_tails = trace_sig_tails && pos(ctx, sig) == mat.max_pos
            l = leadingmonomial(row)
            if iszero(pivots[l])
                pivots[l] = J(i)
                continue
            end
            buffer!(row, buffer)
            should_add_sig_tails && buffer!(mat.sigtail_mat.rows[sig], sig_tail_buffer)
            for (k, c) in enumerate(buffer)
                (iszero(c) || iszero(pivots[k])) && continue
                arit_operations += length(mat.rows[pivots[k]])
                mult = critical_loop!(buffer, mat.rows[pivots[k]], ctx.po.co)

                # add sig tails
                if should_add_sig_tails && pos(ctx, mat.sigs[pivots[k]]) == mat.max_pos
                    add_sig = mat.sigs[pivots[k]]
                    sub_row!(sig_tail_buffer, mat.sigtail_mat.rows[add_sig], mult, ctx.po.co) 
                end
                    
            end
            first_nz, new_row = unbuffer!(buffer, ctx.po.co, J)
            if !(iszero(first_nz))
                pivots[first_nz] = J(i)
            end

            if should_add_sig_tails
                _, new_sig_tail = unbuffer!(sig_tail_buffer, ctx.po.co, J)
                mat.sigtail_mat.rows[sig] = new_sig_tail
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
    first_nz, row
end

function sub_row!(buffer::Vector{Tbuf},
                  pivot_row::Polynomial{J, T},
                  mult::T,
                  ctx::NmodLikeΓ{T, Tbuf}) where {J, T, Tbuf}

    for (j, c) in pivot_row
        buffer[j] = submul(ctx, buffer[j], mult, c)
    end
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

# managing the basis and syzygies after reduction

function new_syz!(ctx::SΓ,
                  sig::MonSigPair{I, M},
                  sig_tail::Polynomial{M, T},
                  pairs::PairSet{I, M, SΓ},
                  H::Syz{I, M}) where {I, M, T, SΓ <: SigPolynomialΓ{I, M, T}}

    new_sig = mul(ctx, sig...)
    ctx(new_sig, zero(eltype(ctx.po)), sig_tail)
    push!(H[new_sig[1]], new_sig[2])
    new_rewriter!(ctx, pairs, new_sig)
end

function new_basis!(ctx::SΓ,
                    sig::MonSigPair{I, M},
                    poly::Polynomial{M, T},
                    sig_tail::Polynomial{M, T},
                    pairs::PairSet{I, M, SΓ},
                    G::Basis{I, M},
                    H::Syz{I, M}) where {I, M, T, SΓ <: SigPolynomialΓ{I, M, T}}

    m, (pos_key, t) = sig
    posit = pos(ctx, sig)
    new_sig = mul(ctx, sig...)
    # add element to basis if any of the following two conditions hold:
    # reductions of initial generators are added
    add_cond_1 = isone(ctx.po.mo[m]) && isone(ctx.po.mo[t]) && !(new_sig[2] in keys(G[posit]))
    # leading term dropped during reduction
    add_cond_2 = lt(ctx.po.mo, leadingmonomial(poly), leadingmonomial(ctx(sig...)[:poly]))
    if add_cond_1 || add_cond_2                 
        @debug "adding $(pretty_print(ctx, sig)) with lm $(pretty_print(ctx.po.mo, leadingmonomial(poly)))"
        ctx(new_sig, poly, sig_tail)
        lm = leadingmonomial(poly)
        new_rewriter!(ctx, pairs, new_sig)
        pairs!(ctx, pairs, new_sig, lm, G, H)
        push!(G[pos_key], (new_sig[2], lm))
    end
end
                    

function new_elems_f5!(ctx::SΓ,
                       mat::F5matrix{I, M, T},
                       pairs::PairSet{I, M, SΓ},
                       G::Basis{I, M},
                       H::Syz{I, M}) where {I, M, T, SΓ <: SigPolynomialΓ{I, M, T}}

    for (i, sig) in enumerate(mat.sigs)
        @inbounds begin
            if pos(ctx, sig) == mat.max_pos
                sig_tail = tail(unindexpolynomial(mat.sigtail_mat.tbl, mat.sigtail_mat.rows[sig]))
            else
                sig_tail = zero(eltype(ctx.po))
            end
            if isempty(mat.rows[i])
                new_syz!(ctx, sig, sig_tail, pairs, H)
            else     
                p = unindexpolynomial(mat.tbl, mat.rows[i])
                new_basis!(ctx, sig, p, sig_tail, pairs, G, H)
            end
        end
    end
end

function new_elems_decomp!(ctx::SΓ,
                           mat::F5matrix{I, M, T},
                           pairs::PairSet{I, M, SΓ},
                           G::Basis{I, M},
                           H::Syz{I, M}) where {I, M, T, SΓ <: SigPolynomialΓ{I, M, T}}
    return
end 
