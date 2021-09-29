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
    
