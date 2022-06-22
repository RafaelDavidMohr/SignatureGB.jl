# SGB TREES

# check whether a is a prefix of b
function is_prefix_vector(a, b)
    length(a) > length(b) && return false
    for (i, x) in enumerate(a)
        x == b[i] && continue
        return false
    end
    return true
end

# How to handle the root nodes?
mutable struct SGBNode{I, M, T}
    ID::I
    sort_ID::I
    # path to node by ID excluding node itself
    path_to::Vector{I}
    # should we hold this explicitly?
    pol::Polynomial{M, T}
    is_branch_node::Bool
    tag::Symbol
    # hold children and parent by ID
    children_id::Vector{I}
    parent_id::I
end


function in_path_to(node1::SGBNode{I, M, T},
                    node2::SGBNode{I, M, T}) where {I, M, T}

    # maybe include node itself in path_to
    isempty(node2.path_to) && return node1.ID == node2.ID
    is_prefix_vector(vcat(node1.path_to, [node1.ID]), node2.path_to)
end

function are_compatible(node1::SGBNode{I, M, T},
                        node2::SGBNode{I, M, T}) where {I, M, T}

    node1.ID == node2.ID || in_path_to(node1, node2) || in_path_to(node2, node1)
end
    
function compare(ID_dict::Dict{I, SGBNode{I, M, T}},
                 node1::SGBNode{I, M, T},
                 node2::SGBNode{I, M, T}) where {I, M, T}

    node1.ID == node2.ID && return false
    
    if in_path_to(node1, node2)
        return true
    end
    if in_path_to(node2, node1)
        return false
    end

    # two different branches -> compare "left" to "right"
    fullpath1 = vcat(node1.path_to, [node1.ID])
    fullpath2 = vcat(node2.path_to, [node2.ID])
    ancestor_pairs = collect(zip(fullpath1, fullpath2))
    common_ancestor_index = findlast(node_ids -> node_ids[1] == node_ids[2], ancestor_pairs)
    if isnothing(common_ancestor_index)
        println(fullpath1)
        println(fullpath2)
        error(":(")
    end
    common_ancestor = fullpath1[common_ancestor_index]
    
    next_in_path1 = fullpath1[common_ancestor_index + 1]
    next_in_path2 = fullpath2[common_ancestor_index + 1]
    return findfirst(id -> id == next_in_path1, ID_dict[common_ancestor].children_id) <
        findfirst(id -> id == next_in_path2, ID_dict[common_ancestor].children_id)
end

function assign_sort_ids!(ID_dict::Dict{I, SGBNode{I, M, T}}) where {I, M, T}

    ids = collect(keys(ID_dict))
    sorted = sortperm(ids, by = id -> ID_dict[id],
                      lt = (node1, node2) -> compare(ID_dict, node1, node2))
    for (i, id) in enumerate(ids[sorted])
        ID_dict[id].sort_ID = i
    end
end
        
function new_node!(parent_id::I,
                   pol::Polynomial{M, T},
                   ID_dict::Dict{I, SGBNode{I, M, T}},
                   tag::Symbol;
                   is_branch_node = false) where {I, M, T}

    id = isempty(keys(ID_dict)) ? one(I) : maximum(keys(ID_dict)) + 1
    if !(iszero(parent_id))
        node = SGBNode{I, M, T}(id, zero(I), vcat(ID_dict[parent_id].path_to, [parent_id]),
                                pol, is_branch_node, tag, I[],
                                parent_id)
        push!(ID_dict[parent_id].children_id, id)
    else
        node = SGBNode{I, M, T}(id, zero(I), I[],
                                pol, is_branch_node, tag, I[],
                                zero(I))
    end
    ID_dict[id] = node
    return node
end

function new_branch_node!(parent_id::I,
                          ID_dict::Dict{I, SGBNode{I, M, T}}) where {I, M, T}
    new_node!(parent_id, zero(Polynomial{M, T}), ID_dict, :branch, is_branch_node = true)
end  

function new_leaf!(parent_id::I,
                   pol::Polynomial{M, T},
                   ID_dict::Dict{I, SGBNode{I, M, T}},
                   tag::Symbol;
                   is_branch_node = false) where {I, M, T}
    
    node = new_node!(parent_id, pol, ID_dict, tag, is_branch_node = is_branch_node)
    assign_sort_ids!(ID_dict)
    return node
end

function insert_before!(before::SGBNode{I, M, T},
                        pol::Polynomial{M, T},
                        ID_dict::Dict{I, SGBNode{I, M, T}},
                        tag::Symbol) where {I, M, T}

    if !(iszero(before.parent_id))
        deleteat!(ID_dict[before.parent_id].children_id,
                  findfirst(id -> id == before.ID, ID_dict[before.parent_id].children_id))
    end
    node = new_node!(before.parent_id, pol, ID_dict, tag)
    before.parent_id = node.ID
    push!(node.children_id, before.ID)
    push!(before.path_to, node.ID)
    set_path_subtree!(before, ID_dict)
    assign_sort_ids!(ID_dict)
    return node
end

function copy_subtree!(node::SGBNode{I, M, T},
                       parent_id::I,
                       ID_dict::Dict{I, SGBNode{I, M, T}}) where {I, M, T}

    new_ids = I[]
    new_branch_node_ids = I[]
    for child in map(id -> ID_dict[id], node.children_id)
        child_copy = new_node!(parent_id, copy(child.pol), ID_dict, child.tag, is_branch_node = child.is_branch_node)
        if child.is_branch_node
            push!(new_branch_node_ids, child_copy.ID)
        else
            push!(new_ids, child_copy.ID)
        end
        new_ids_child, new_branch_node_ids_child = copy_subtree!(child, child.ID, ID_dict)
        append!(new_ids, new_ids_child)
        append!(new_branch_node_ids, new_branch_node_ids_child)
    end
    return new_ids, new_branch_node_ids
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

#--- SPLITTING RULES ---#

function split_on_tag_f!(ID_dict::Dict{I, SGBNode{I, M, T}},
                         f_node_id::I,
                         zd_to_insert::Polynomial{M, T}) where {I, M, T}

    new_ids, new_branch_node_ids = copy_subtree!(ID_dict[f_node_id],
                                                 ID_dict[f_node_id].parent_id,
                                                 ID_dict)

    new_cleaners = I[]
    for new_branch_node_id in new_branch_node_ids
        push!(new_cleaners, new_leaf!(new_branch_node_id, zd_to_insert, ID_dict, :cleaner).ID)
    end

    push!(new_ids, insert_before!(ID_dict[f_node_id], zd_to_insert, ID_dict, :g).ID)
    return new_ids, new_branch_node_ids, new_cleaners
end 
