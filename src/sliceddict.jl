using Dictionaries

"""
    SlicedInd{I, K}(::Dictionary{I, Vector{K}})

Subtype of `AbstractIndices{Tuple{I, K}}` so that all tuples `(i, k)` with `i` equal
to a given value can be accessed in constant time.

"""
mutable struct SlicedInd{I, K} <: AbstractIndices{Tuple{I, K}}
    ind::Dictionary{I, Vector{K}}
end

"""
    SlicedInd(::Vector{Tuple{I, K}})

Construct a `SlicedInd{I, K}` object from a given Vector of Tuples.
"""
function SlicedInd(ind::Vector{Tuple{I, K}}) where {I, K}
    dct = Dictionary{I, Vector{K}}()
    for (i, k) in ind
        try
            insert!(dct, i, [k])
        catch
            push!(dct[i], k)
        end
    end
    SlicedInd(dct)
end

function Base.iterate(Sl::SlicedInd, s...)
    iterate([(i, k) for i in Base.keys(Sl.ind) for k in Sl.ind[i]], s...)
end

function Base.in(i::Tuple{I, K}, Sl::SlicedInd{I, K}) where {I, K}
    Base.in(i[1], Base.keys(Sl.ind)) && Base.in(i[2], Sl.ind[i[1]])
end

function Base.length(Sl::SlicedInd)
    sum([Base.length(k) for k in values(Sl.ind)])
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
    dct = Dictionary{I, Dictionary{K, V}}(is, [Dictionary{K, V}() for _ in 1:Base.length(is)])
    for (j, (i, k)) in enumerate(ind)
        insert!(dct[i], k, vs[j])
    end
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

function Base.keys(S::SlicedDict)
    ks = Base.keys(S.data)
    SlicedInd(Dictionary(ks, [collect(Base.keys(S.data[i])) for i in ks]))
end

function Base.isassigned(S::SlicedDict{I, K}, i::Tuple{I, K}) where {I, K}
    Base.isassigned(S.data, i[1]) && Base.isassigned(S.data[i[1]], i[2])
end
