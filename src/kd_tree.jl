# Binary tree as per example in AbstractTrees

using AbstractTrees

# divmask type, sigtype
mutable struct Kd_node{I, M}
    # mask
    mask_monomial::M

    # stored monomials if it is a leaf
    basis_elements::SlicedInd{I, M}
    
    # tree structure
    left::Kd_node{I, M}
    right::Kd_node{I, M}

    Kd_node{I, M}(m::M) where {I, M} = new{I, M}(m)
    Kd_node{I, M}(bs_elem::SlicedInd{I, M}) where {I, M} = new{I, M}(zero(M), bs_elem)
end

function Kd_node(ms::Vector{M},
                 pos_t::Type{I}) where {I, M}
    isempty(ms) && return Kd_node{I, M}(SlicedInd(Tuple{I, M}[]))
    nd = Kd_node{I, M}(first(ms))
    nd.left = Kd_node(ms[2:end], pos_t)
    nd.right = Kd_node(ms[2:end], pos_t)
    nd
end

function AbstractTrees.children(node::Kd_node)
    if isdefined(node, :left)
        return (node.left, node.right)
    end
    return ()
end

Base.eltype(::Type{<:TreeIterator{Kd_node{I, M}}}) where {I, M} = Kd_node{I, M}
Base.IteratorEltype(::Type{<:TreeIterator{Kd_node{I, M}}}) where {I, M} = Base.HasEltype()

# divisor related functions

function insert_new_basis_element!(ctx::SigPolynomialΓ{I, M},
                                   tree::Kd_node{I, M},
                                   basis_elem::Tuple{I, M}) where {I, M}

    @assert basis_elem in keys(ctx.tbl) "$(basis_elem) not registered in sigtable"
    if isdefined(tree, :basis_elements)
        insert!(tree.basis_elements, basis_elem)
    elseif divides(ctx.po.mo, tree.mask_monomial, leadingmonomial(ctx, basis_elem))
        insert_new_basis_element!(ctx, tree.left, basis_elem)
    else
        insert_new_basis_element!(ctx, tree.right, basis_elem)
    end
end

function div_query(ctx::SigPolynomialΓ{I, M},
                   tree::Kd_node{I, M},
                   m::M) where {I, M}

    if isdefined(tree, :basis_elements)
        return filter(be -> divides(ctx.po.mo, leadingmonomial(ctx, be), m),
                      tree.basis_elements)
    elseif divides(ctx.po.mo, tree.mask_monomial, m)
        return div_query(ctx, tree.left, m)
    else
        return div_query(ctx, tree.right, m)
    end
end
                   
