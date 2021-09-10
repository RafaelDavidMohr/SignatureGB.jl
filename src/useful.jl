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

@generated function bitw_and(a::BitArray, b::BitArray, ::Val{N}) where N
    quote
        $([:(~(a[$i] & b[$i]) && return false) for i in 1:N]...)
    end
end
