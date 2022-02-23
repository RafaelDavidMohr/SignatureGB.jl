using Logging

const Verbose1 = Logging.LogLevel(-1250)
const Verbose2 = Logging.LogLevel(-1750)

mutable struct Timings
    time_core_loop::Float64
    time_intermed_clean::Float64
    time_final_clean::Float64
end

new_timings() = Timings(0.0, 0.0, 0.0)

mutable struct Info
    arit_ops_groebner::Int
    arit_ops_module::Int
    arit_ops_interred::Int
    interred_mat_size_rows::Int
    interred_mat_size_columns::Int
    num_zero_red::Int
    max_deg_reached::Int
    gb_size_bef_interred::Int
    gb_size_after_interred::Int
end

new_info() = Info([0 for _ in 1:9]...)

mutable struct SGBLogger{I, L <: AbstractLogger} <: AbstractLogger
    logger::L
    verbose_level::Int
    # TODO: data to record
    timings::Timings
    info_per_index::Dict{I, Info}
end

# TODO: put in initial data, based on sigpolynomialctx
function SGBLogger(ctx::SigPolynomialΓ{I}; verbose = 0) where I
    info_per_index = Dict{I, Info}([(i, new_info()) for i in keys(ctx.f5_indices)])
    timings = new_timings()
    if iszero(verbose)
        return SGBLogger(global_logger(), Logging.LogLevel(0), info_per_index, timings)
    elseif isone(verbose)
        return SGBLogger(global_logger(), Verbose1, info_per_index, timings)
    elseif verbose == 2
        return SGBLogger(global_logger(), Verbose2, info_per_index, timings)
    else
        error("choose a verbose level among 0, 1 or 2")
    end
end

function Logging.handle_message(logger::SGBLogger, level, args...;
                                # TODO: put relevant key value pairs
                                kwargs...)
    
    if level == Verbose1
        # TODO: record data
        continue
    elseif level == Verbose2
        # TODO: record data, format message
    end
    # fallback to global logger
    Logging.handle_message(logger.logger, level, args..., kwargs...)
end
            
function Logging.shouldlog(logger::SGBLogger, level, args...)
    level in [Verbose1, Verbose2] && return true
    Logging.shouldlog(logger.logger, args...)
end

Logging.min_enabled_level(logger::SGBLogger) = minimum(logger.logger.level, logger.verbose_level)

function Logging.catch_exceptions(logger::SGBLogger)
    Logging.catch_exceptions(logger.logger)
end
