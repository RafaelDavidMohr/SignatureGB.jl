using Combinatorics

mutable struct SimpleMatrix{I, M, T, J}
    rows::Dict{MonSigPair{I, M}, Polynomial{J, T}}
    tbl::EasyTable{M, J}
end

mutable struct F5matrix{I, M, T, J}
    sigtail_mat::SimpleMatrix{I, M, T, J}
    sigs_rows::OrderedDict{MonSigPair{I, M}, Polynomial{J, T}}
    tbl::EasyTable{M, J}
    max_pos::I
    tag::Symbol
end

function f5matrix(ctx::SigPolynomialΓ{I, M, T},
                  mons::Vector{M},
                  row_sigs::MonSigSet{I, M}) where {I, M, T}

    max_pos = pos(ctx, last(row_sigs))
    tag = gettag(ctx, last(row_sigs))
    tbl = easytable(mons)
    sigtail_mons = M[]

    sigs_rows = Array{Tuple{MonSigPair{I, M}, Polynomial{ind_type(tbl), T}}}(undef, length(row_sigs))
    sigtail_sigs_rows_unind = Tuple{MonSigPair{I, M}, Polynomial{M, T}}[]
    for (i, sig) in enumerate(row_sigs)
        sig_dat = ctx(sig...)
        sigs_rows[i] = (sig, indexpolynomial(tbl, sig_dat[:poly]))
        if pos(ctx, sig) == max_pos
            sig_tail = project(mul(ctx, sig...), sig_dat[:sigtail])
            append!(sigtail_mons, sig_tail.mo)
            push!(sigtail_sigs_rows_unind, (sig, sig_tail))
        end
    end

    sigtail_tbl = easytable(sort(unique(sigtail_mons),
                                 rev=true,
                                 order=order(ctx.po.mo)))
    sigtail_sigs_rows = Dict([(sig, indexpolynomial(sigtail_tbl, p))
                              for (sig, p) in sigtail_sigs_rows_unind])

    F5matrix(SimpleMatrix(sigtail_sigs_rows, sigtail_tbl),
             OrderedDict(sigs_rows),
             tbl,
             max_pos,
             tag)
end

function check_row_echelon(mat::F5matrix)
    for ((s, p1), (t, p2)) in combinations(mat.sigs_rows, 2)
        (isempty(p1) || isempty(p2)) && continue
        leadingmonomial(p1) == leadingmonomial(p2) && return false
    end
    return true
end

# for printing matrices
function mat_show(mat)
    mat_vis = zeros(Int, length(mat.sigs_rows), length(mat.tbl.val))
    for (i, (sig, row)) in enumerate(mat.sigs_rows)
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
    pivots = collect(Base.Iterators.repeated(nullmonsigpair(ctx), n_cols))
    buffer = zeros(buftype(ctx.po.co), n_cols)
    sig_tail_buffer = zeros(buftype(ctx.po.co), length(mat.sigtail_mat.tbl))
    arit_operations_groebner = 0
    arit_operations_module_overhead = 0

    @inbounds begin
        for (sig, row) in mat.sigs_rows
            should_add_sig_tails = trace_sig_tails && pos(ctx, sig) == mat.max_pos
            l = leadingmonomial(row)
            if isnull(pivots[l])
                pivots[l] = sig
                continue
            end
            buffer!(row, buffer)
            should_add_sig_tails && buffer!(mat.sigtail_mat.rows[sig], sig_tail_buffer)
            for (k, c) in enumerate(buffer)
                (iszero(c) || isnull(pivots[k])) && continue
                arit_operations_groebner += length(mat.sigs_rows[pivots[k]])
                mult = critical_loop!(buffer, mat.sigs_rows[pivots[k]], ctx.po.co)

                # add sig tails
                if should_add_sig_tails && pos(ctx, pivots[k]) == mat.max_pos
                    arit_operations_module_overhead += length(mat.sigtail_mat.rows[pivots[k]])
                    sub_row!(sig_tail_buffer, mat.sigtail_mat.rows[pivots[k]], mult, ctx.po.co) 
                end
                    
            end
            first_nz, new_row = unbuffer!(buffer, ctx.po.co, J)
            if !(iszero(first_nz))
                pivots[first_nz] = sig
            end

            if should_add_sig_tails
                _, new_sig_tail = unbuffer!(sig_tail_buffer, ctx.po.co, J)
                mat.sigtail_mat.rows[sig] = new_sig_tail
            end
            
            mat.sigs_rows[sig] = new_row
        end
    end
    arit_operations_groebner, arit_operations_module_overhead
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
    new_sig = mul(ctx, sig...)
    # add element to basis if any of the following two conditions hold:
    # reductions of initial generators are added
    add_cond_1 = isone(ctx.po.mo[m]) && isone(ctx.po.mo[t]) && !(t in keys(G[pos_key]))
    # leading term dropped during reduction
    add_cond_2 = lt(ctx.po.mo, leadingmonomial(poly), mul(ctx.po.mo, m, leadingmonomial(ctx, (pos_key, t))))
    if add_cond_1 || add_cond_2                 
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

    for (sig, row) in mat.sigs_rows
        @inbounds begin
            if pos(ctx, sig) == mat.max_pos
                sig_tail = tail(unindexpolynomial(mat.sigtail_mat.tbl, mat.sigtail_mat.rows[sig]))
                if isempty(row)
                    new_syz!(ctx, sig, sig_tail, pairs, H)
                else     
                    p = unindexpolynomial(mat.tbl, row)
                    new_basis!(ctx, sig, p, sig_tail, pairs, G, H)
                end
            end
        end
    end
    pairs
end

function new_elems_decomp!(ctx::SΓ,
                           mat::F5matrix{I, M, T},
                           pairs::PairSet{I, M, SΓ},
                           G::Basis{I, M},
                           H::Syz{I, M}) where {I, M, T, SΓ <: SigPolynomialΓ{I, M, T}}

    mat.tag != :f && return new_elems_f5!(ctx, mat, pairs, G, H)
    
    zero_red = filter(sig_row -> isempty(sig_row[2]) && gettag(ctx, sig_row[1]) == :f,
                      mat.sigs_rows)
    isempty(zero_red) && return new_elems_f5!(ctx, mat, pairs, G, H)

    # insert g's s.t. g*f in I
    for (j, (sig, _)) in enumerate(zero_red)
        prj = unindexpolynomial(mat.sigtail_mat.tbl, mat.sigtail_mat.rows[sig])
        ctx(mul(ctx, sig...), zero(eltype(ctx.po)), tail(prj))
        new_gen!(ctx, pos(ctx, sig) + I(j) - one(I), :g, prj)
    end
    
    filter!(pos_elems -> ctx.ord_indices[pos_elems[1]][:position] < mat.max_pos, G)
    pairs = pairset(ctx)
    for posit_key in keys(ctx.ord_indices)
        sg = (posit_key, one(ctx.po.mo))
        if pos(ctx, sg) >= mat.max_pos
            pair!(ctx, pairs, sg)
            G[posit_key] = Tuple{M, M}[]
            if !(posit_key in keys(H))
                H[posit_key] = Tuple{M, M}[]
            end
        end
    end
    pairs
end 
