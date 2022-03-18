using Logging
using DataFrames

const Verbose1 = Logging.LogLevel(-1250)
const Verbose2 = Logging.LogLevel(-1750)

mutable struct Timings
    time_pair_gen::Float64
    time_symbolic_pp::Float64
    time_reduction::Float64
end

new_timings() = Timings(0.0, 0.0, 0.0)

# mutable struct Info
#     pairs_eliminated_koszul::Int
#     pairs_eliminated_syz::Int
#     arit_ops_groebner::Int
#     arit_ops_module::Int
#     arit_ops_interred::Int
#     interred_mat_size_rows::Int
#     interred_mat_size_columns::Int
#     num_zero_red::Int
#     max_deg_reached::Int
#     gb_size_bef_interred::Int
#     gb_size_after_interred::Int
# end

new_info() = Info([0 for _ in 1:9]...)

mutable struct SGBLogger{I, L <: AbstractLogger} <: AbstractLogger
    logger::L
    verbose_level::Logging.LogLevel
    # TODO: data to record
    core_info::DataFrame
    stop_watch_start::Float64
    timings::Timings
end

# TODO: put in initial data, based on sigpolynomialctx
function SGBLogger(ctx::SigPolynomialΓ{I}; verbose = 0) where I
    # probably shouldnt do this
    Logging.disable_logging(Logging.LogLevel(-1751))
    verbose_table = [Logging.LogLevel(0), Verbose1, Verbose2]
    # info_per_index = Dict{I, Info}([(i, new_info()) for i in keys(ctx.f5_indices)])
    timings = new_timings()
    if ctx.track_module_tags == [:to_sat]
        return SGBLogger{I, typeof(global_logger())}(global_logger(), verbose_table[verbose + 1],
                                                     DataFrame(sig_deg = Int64[], indx = Int64[], tag = Symbol[], sel = Int64[],
                                                               pairs = Int64[], mat = Tuple{Int64, Int64}[],
                                                               density = Float32[], arit_ops = Int64[], syz = Int64[],
                                                               new_elems = Int64[], time = Float64[]),
                                                     zero(Float64), timings)
    else
        return SGBLogger{I, typeof(global_logger())}(global_logger(), verbose_table[verbose + 1],
                                                     DataFrame(sig_deg = Int64[], sel = Int64[],
                                                               pairs = Int64[], mat = Tuple{Int64, Int64}[],
                                                               density = Float32[], arit_ops = Int64[], syz = Int64[],
                                                               new_elems = Int64[], time = Float64[]),
                                                     zero(Float64), timings)
    end
end

function add_info_row!(logger::SGBLogger)

    tuples = Dict([(:sig_deg, 0), (:sel, 0), (:pairs, 0), (:mat, (0,0)),
                   (:density, zero(Float32)), (:arit_ops, 0),
                   (:syz, 0), (:new_elems, 0), (:time, zero(Float64))])
    push!(logger.core_info, tuples, cols = :subset)
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
                                add_row = false,
                                curr_index = 0,
                                sig_degree = -1,
                                nselected = 0,
                                npairs = 0,
                                nz_entries = 0,
                                mat_size = (0, 0),
                                indx = 0,
                                tag = nothing,
                                arit_ops = 0,
                                new_syz = false,
                                new_basis = false,
                                start_time_core = 0.0,
                                end_time_core = 0.0,
                                kwargs...)

    if level == Verbose1
        if curr_index != 0
            println("index $(curr_index), sig degree $(sig_degree)")
        end
    elseif level == Verbose2
        # TODO: record data, format message
        if add_row
            add_info_row!(logger)
            set_info_row!(logger, (:syz, 0), (:new_elems, 0))
        end
        if sig_degree >= 0
            set_info_row!(logger, (:sig_deg, sig_degree))
        end
        if nselected > 0
            set_info_row!(logger, (:sel, nselected))
        end
        if npairs != 0
            set_info_row!(logger, (:pairs, npairs))
        end
        if mat_size != (0, 0)
            set_info_row!(logger, (:mat, mat_size),
                          (:density, round(nz_entries / *(mat_size...), digits = 2)))
        end
        if nz_entries != 0
            mat_size = logger.core_info[nrow(logger.core_info), :][:mat]
            set_info_row!(logger, (:mat, mat_size),
                          (:density, round(nz_entries / *(mat_size...), digits = 2)))
        end
        if indx != 0
            set_info_row!(logger, (:indx, indx))
        end
        if tag != nothing
            set_info_row!(logger, (:tag, tag))
        end
        if arit_ops > 0
            inc_row!(logger, :arit_ops, arit_ops)
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
