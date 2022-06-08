# THIS FILE IS FOR PROTOTYPING F5 GRAPHS

using Graphs

# Construction

function example()
    g = SimpleDiGraph()
    [add_vertex!(g) for _ in 1:3]
    add_edge!(g, 1, 2)
    add_edge!(g, 2, 3)
    return g
end

function insert_before!(graph, node)
    @assert has_vertex(graph, node)
    old_before = inneighbors(g, node)
    add_vertex!(g)
    if isempty(old_before)
        add_edge!(g, nv(g), node)
    else
        old_parent = first(old_before)
        rem_edge!(g, old_parent, node)
        add_edge!(g, nv(g), node)
        add_edge!(g, old_parent, nv(g))
    end
    return nv(g)
end

function all_children(graph, node)
    vcat(outneighbors(graph, node), [all_children(graph, vert) for vert in outneighbors(graph, node)]...)
end
    
function copy_sub_tree_and_parent_append(graph, node)
    children = all_children(graph, node)
    subgraph, vlist = induced_subgraph(graph, children)
    parent = first(inneighbors(graph, node))
    result = blockdiag(graph, subgraph)
    for v in outneighbors(graph, node)
        add_edge!(result, parent, findfirst(w -> w == v, vlist) + nv(graph))
    end
    # maybe do some equation copying
    return result
end
    
#=
To do term comparison: Have a Dict Nodes(F5tree) -> all_nodes smaller than a given node as a set!
This data structure needs to be managed during node insertion.
What about copying of subtrees?
=#
