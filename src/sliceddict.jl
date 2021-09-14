using Dictionaries

"""
    SlicedInd{I, K}(::Dictionary{I, Vector{K}})

Subtype of `AbstractIndices{Tuple{I, K}}` so that all tuples `(i, k)` with `i` equal
to a given value can be accessed in constant time.

"""
mutable struct SlicedInd{I, K} <: AbstractIndices{Tuple{I, K}}
    ind::Dictionary{I, Indices{K}}
end

"""
    SlicedInd(::Vector{Tuple{I, K}})

Construct a `SlicedInd{I, K}` object from a given Vector of Tuples.
"""
function SlicedInd(ind::Vector{Tuple{I, K}}) where {I, K}
    dct = Dictionary{I, Indices{K}}()
    for (i, k) in ind
        if i in keys(dct)
            Base.insert!(dct[i], k)
        else
            Base.insert!(dct, i, Indices([k]))
        end
    end
    SlicedInd(dct)
end

Base.getindex(Sl::SlicedInd{I}, i::I) where I = Sl.ind[i]

function Base.iterate(Sl::SlicedInd, s...)
    iterate([(i, k) for i in Base.keys(Sl.ind) for k in Sl.ind[i]], s...)
end

function Base.in(i::Tuple{I, K}, Sl::SlicedInd{I, K}) where {I, K}
    Base.in(i[1], Base.keys(Sl.ind)) && Base.in(i[2], Sl.ind[i[1]])
end

function Base.length(Sl::SlicedInd)
    sum([Base.length(k) for k in values(Sl.ind)])
end

Dictionaries.isinsertable(Sl::SlicedInd) = true
function Base.insert!(Sl::SlicedInd{I, K}, ind::Tuple{I, K}) where {I, K}
    if ind[1] in keys(Sl.ind)
        Base.insert!(Sl.ind[ind[1]], ind[2])
    else
        Base.insert!(Sl.ind, ind[1], Indices([ind[2]]))
    end
end

function Base.delete!(Sl::SlicedInd{I, K}, ind::Tuple{I, K}) where {I, K}
    delete!(Sl.ind[ind[1]], ind[2])
    isempty(Sl.ind[ind[1]]) && delete!(Sl.ind, ind[1])
end

"""
    SlicedDict{I, K}(::Dictionary{I, Dictionary{K, V}})

Subtype of `AbstractDictionary{Tuple{I, K}, V}` so that all pairs `(i, k) => v`
 with `i` equal to a given value can be accessed in constant time.

"""
mutable struct SlicedDict{I, K, V} <: AbstractDictionary{Tuple{I, K}, V}
    data::Dictionary{I, Dictionary{K, V}}
end


"""
    SlicedDict(ind::SlicedInd{I, K}, vs::Vector{V})

Construct a `SlicedDict{I, K, V}` with keys `ind` and values `vs`. 
"""
function SlicedDict(ind::SlicedInd{I, K}, vs::Vector{V}) where {I, K, V}
    is = Base.keys(ind.ind)
    slices = vcat([0], [length(ind[i]) for i in is])
    for i in eachindex(slices)[2:end]
        slices[i] = slices[i] + slices[i-1]
    end
    dct = Dictionary(is, [Dictionary(ind[i], vs[slices[j]+1:slices[j+1]]) for (j, i) in enumerate(is)])
    # for (j, (i, k)) in enumerate(ind)
    #     println("i'm iterating")
    #     Base.insert!(dct[i], k, vs[j])
    # end
    SlicedDict(dct)
end

"""
    SlicedDict(ind::Vector{Tuple{I, K}}, vs::Vector{V})

Construct a `SlicedDict{I, K, V}` with keys `ind` and values `vs`.
"""
function SlicedDict(ind::Vector{Tuple{I, K}}, vs::Vector{V}) where {I, K, V}
    SlicedDict(SlicedInd(ind), vs)
end
        
function Base.getindex(S::SlicedDict{I, K}, i::Tuple{I, K}) where {I, K}
    Base.getindex(Base.getindex(S.data, i[1]), i[2])
end

Base.getindex(S::SlicedDict{I}, i::I) where I = S.data[i]

function Base.keys(S::SlicedDict)
    ks = Base.keys(S.data)
    SlicedInd(Dictionary(ks, [Indices(collect(Base.keys(S.data[i]))) for i in ks]))
end

function Base.isassigned(S::SlicedDict{I, K}, i::Tuple{I, K}) where {I, K}
    Base.isassigned(S.data, i[1]) && Base.isassigned(S.data[i[1]], i[2])
end

Dictionaries.issettable(S::SlicedDict) = true
Dictionaries.isinsertable(S::SlicedDict) = true

function Base.setindex!(S::SlicedDict{I, K, V}, val::V, ind::Tuple{I, K}) where {I, K, V}
    setindex!(S.data[ind[1]], val, ind[2])
end

function Base.insert!(S::SlicedDict{I, K, V}, ind::Tuple{I, K}, val::V) where {I, K, V}
    if ind[1] in keys(S.data)
        Base.insert!(S.data[ind[1]], ind[2], val)
    else
        Base.insert!(S.data, ind[1], Dictionary([ind[2]], [val]))
    end
end

function Base.delete!(S::SlicedDict{I, K}, ind::Tuple{I, K}) where {I, K}
    Base.delete!(S.data[ind[1]], ind[2])
end
