using Oscar
using AbstractAlgebra

"""
    @default ex, fs

For each `f` in `fs` declare a method `f(args...; kwargs...) = f(ex, args...; kwargs)`.
"""

macro default(ex, fs)
    ex = esc(ex)
    fs = isexpr(fs, :tuple) ? map(esc, fs.args) : [esc(fs)]
    quote
        $([:($f(args...; kwargs...) = $f($ex, args...; kwargs...)) for f in fs]...)
    end
end

#.. Helpers for BitVectors

@generated function bitcheck(a::BitArray, b::BitArray, ::Val{N}) where N
    quote
        $([:(b[$i] < a[$i] && return false) for i in 1:N]...)
        return true
    end
end

function even_partition(i, nums)
    fl = typeof(i)(floor(i / nums))
    part = repeat([fl], nums)
    while sum(part) != i
        ind = rand(1:nums)
        part[ind] += 1
    end
    part
end

function even_between(a, b, nums)
    part = even_partition(b - a, nums)
    part_2 = similar(part)
    curr = a
    for (i, p) in enumerate(part)
        part_2[i] = curr
        curr += p
    end
    part_2
end

function mac_bound(I::Vector{P}) where {P <: AbstractAlgebra.MPolyElem}
    I_sorted = sort(I, by = p -> Oscar.total_degree(p), rev = true)
    l = min(ngens(parent(first(I))) + 1, length(I))
    sum([total_degree(I_sorted[j]) for j in 1:l]) - l + 1
end
    
    
