# SGB TREES

# check whether a is a prefix of b
function is_prefix_vector(a, b)
    for (i, x) in enumerate(a)
        x == b[i] && continue
        return false
    end
    return true
end

# How to handle the root nodes?
mutable struct SGBNode{I, M, T}
    ID::I
    # path to node by ID excluding node itself
    path_to::Vector{I}
    # should we hold this explicitly?
    pol::Polynomial{M, T}
    is_branch_node::Bool
    tag::Symbol
    # hold children and parent by ID
    children_id::Set{I}
    parent_id::I
end

function are_compatible(node1::SGBNode{I, M, T},
                        node2::SGBNode{I, M, T}) where {I, M, T}

    # maybe include node itself in path_to
    is_prefix_vector(vcat(node1.path_to, [node1.ID]), node2.path_to)
end

function in_branch_before(node1::SGBNode{I, M, T},
                          node2::SGBNode{I, M, T}) where {I, M, T}

    length(node1.path_to) < length(node2.path_to) && are_compatible(node1, node2)
end

function new_node!(parent_id::I,
                   pol::Polynomial{M, T},
                   ID_dict::Dict{I, SGBNode{I, M, T}},
                   tag::Symbol;
                   is_branch_node = false) where {I, M, T}

    id = maximum(keys(ID_dict)) + 1
    if !(iszero(parent_id))
        node = SGBNode{I, M, T}(id, vcat(ID_dict[parent_id].path_to, [parent_id]),
                                pol, is_branch_node, tag, Set(I[]),
                                parent_id)
        push!(ID_dict[parent_id].children_id, id)
    else
        node = SGBNode{I, M, T}(id, I[],
                                pol, is_branch_node, tag, Set(I[]),
                                zero(I))
    end
    ID_dict[id] = node
    return node
end

function new_root!(ID_dict::Dict{I, SGBNode{I, M, T}}) where {I, M, T}
    new_node!(zero(I), zero(Polynomial{M, T}), ID_dict, :root, is_branch_node = true)
end  

function insert_before!(before::SGBNode{I, M, T},
                        pol::Polynomial{M, T},
                        ID_dict::Dict{I, SGBNode{I, M, T}},
                        tag::Symbol) where {I, M, T}

    if !(iszero(before.parent_id))
        delete!(ID_dict[before.parent_id].children, before.ID)
    end
    node = new_node!(before.parent_id, pol, ID_dict, tag)
    before.parent_id = node.ID
    before.path_to[end] = node.ID
    set_path_subtree!(before)
    return node
end

# set the path to the subtree with root "node" (without setting path of "node" itself)
function set_path_subtree!(node::SGBNode{I, M, T},
                           ID_dict::Dict{I, SGBNode{I, M, T}}) where {I, M, T}
    isempty(node.children_id) && return
    for child_id in node.children_id
        ID_dict[child_id].path_to = vcat(node.path_to, [node.ID])
        set_path_subtree!(ID_dict[child_id], ID_dict)
    end
end
