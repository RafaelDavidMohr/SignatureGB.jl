using Logging
using DataFrames

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
    verbose_level::Logging.LogLevel
    # TODO: data to record
    core_info::DataFrame
    stop_watch_start::Float64
    timings::Timings
    info_per_index::Dict{I, Info}
end

# TODO: put in initial data, based on sigpolynomialctx
function SGBLogger(ctx::SigPolynomialΓ{I}; verbose = 0) where I
    # probably shouldnt do this
    Logging.disable_logging(Logging.LogLevel(-1751))
    verbose_table = [Logging.LogLevel(0), Verbose1, Verbose2]
    info_per_index = Dict{I, Info}([(i, new_info()) for i in keys(ctx.f5_indices)])
    timings = new_timings()
    try
        return SGBLogger(global_logger(), verbose_table[verbose + 1],
                         DataFrame(sig_deg = Int64[], sel = Int64[],
                                   pairs = Int64[], mat = Tuple{Int64, Int64}[],
                                   density = Float32[], syz = Int64[],
                                   new_elems = Int64[], time = Float64[]),
                         zero(Float64), timings, info_per_index)
    catch KeyError
        error("choose a verbose level among 0, 1 or 2")
    end
end

function add_info_row!(logger::SGBLogger,
                       tuples...)
    
    push!(logger.core_info, Dict(collect(tuples)), cols = :subset)
end

function set_info_row!(logger::SGBLogger,
                       tuples...)

    for (name, info) in collect(tuples)
        logger.core_info[nrow(logger.core_info), :][name] = info
    end
end

function inc_row!(logger::SGBLogger,
                  name,
                  val)
    logger.core_info[nrow(logger.core_info), :][name] += val
end

function inc_row!(logger::SGBLogger,
                  name)
    inc_row!(logger, name, 1)
end

function Logging.handle_message(logger::SGBLogger, level, message, _module, group, id, file, line;
                                # TODO: put relevant key value pairs
                                sig_degree = -1,
                                nselected = 0,
                                npairs = 0,
                                nz_entries = 0,
                                mat_size = (0, 0),
                                new_syz = false,
                                new_basis = false,
                                start_time_core = 0.0,
                                end_time_core = 0.0,
                                kwargs...)

    if level == Verbose1
        # TODO: record data
    elseif level == Verbose2
        # TODO: record data, format message
        if sig_degree >= 0 && nselected > 0
            add_info_row!(logger, (:sig_deg, sig_degree), (:sel, nselected), (:pairs, npairs),
                          (:syz, 0), (:new_elems, 0))
            return
        end
        if mat_size != (0, 0)
            set_info_row!(logger, (:mat, mat_size),
                          (:density, round(nz_entries / *(mat_size...), digits = 2)))
        end
        if new_syz
            inc_row!(logger, :syz)
        end
        if new_basis
            inc_row!(logger, :new_elems)
        end
        if start_time_core != 0.0
            logger.stop_watch_start = start_time_core
        end
        if end_time_core != 0.0
            set_info_row!(logger, (:time, round(end_time_core - logger.stop_watch_start, digits = 2)))
            logger.stop_watch_start = 0.0
        end
    end
    # fallback to global logger
    if level >= Logging.min_enabled_level(logger.logger)
        Logging.handle_message(logger.logger, level, message, _module, group, id, file, line; kwargs...)
    end
end
            
function Logging.shouldlog(logger::SGBLogger, level, args...)
    if level in [Verbose1, Verbose2]
        return true
    end
    Logging.shouldlog(logger.logger, level, args...)
end

Logging.min_enabled_level(logger::SGBLogger) = min(Logging.min_enabled_level(logger.logger), logger.verbose_level)

function Logging.catch_exceptions(logger::SGBLogger)
    Logging.catch_exceptions(logger.logger)
end
