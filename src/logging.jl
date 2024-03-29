using Logging
using DataFrames

const Verbose1 = Logging.LogLevel(-250)
const Verbose2 = Logging.LogLevel(-750)

mutable struct Timings
    time_pair_gen::Float64
    time_symbolic_pp::Float64
    time_reduction::Float64
end

new_timings() = Timings(0.0, 0.0, 0.0)

new_info() = Info([0 for _ in 1:9]...)

mutable struct SGBLogger{I, L <: AbstractLogger} <: AbstractLogger
    logger::L
    verbose_level::Logging.LogLevel
    core_info::DataFrame
    stop_watch_start::Float64
    timings::Timings
end

function printout(logger::SGBLogger)

    show(logger.core_info, show_row_number = false, allrows = true, allcols = true)
    print("\n")
    arit_ops = 0
    for row in eachrow(logger.core_info)
        arit_ops += row[:arit_ops]
    end
    println("arithmetic operations: $(arit_ops)")
end

function SGBLogger(ctx::SigPolynomialΓ{I};
                   task = :sgb,
                   verbose = 0,
                   f5c = false,
                   kwargs...) where I
    # probably shouldnt do this
    to_disable = min(Logging.LogLevel(-751), LogLevel(Logging.min_enabled_level(current_logger()).level - 1))
    Logging.disable_logging(to_disable)
    verbose_table = [Logging.LogLevel(0), Verbose1, Verbose2]
    timings = new_timings()

    core_info = DataFrame(sig_deg = Int64[], min_deg = Int64[], sel = Int64[],
                          pairs = Int64[], mat = Tuple{Int64, Int64}[],
                          density = Float32[], arit_ops = Int64[], syz = Int64[],
                          new = Int64[], size = Int64[], time = Float64[])
    
    if task == :sat || task == :decomp
        insertcols!(core_info, :tag => Symbol[], :indx_hash => Int64[], :indx => Int64[])
    elseif mod_order(ctx) == :POT || mod_order(ctx) == :DPOT
        insertcols!(core_info, :indx => Int64[])
    elseif mod_order(ctx) == :SCHREY || mod_order(ctx) == :DPOT
        insertcols!(core_info, :sig_deg, :sugar_deg => Int64[],
                    after = true)
    end
    if f5c
        insertcols!(core_info, :size, :size_aft => Int64[],
                    after = true)
    end
    return SGBLogger{I, typeof(current_logger())}(current_logger(), verbose_table[verbose + 1], core_info,
                                                  zero(Float64), timings)
end

function add_info_row!(logger::SGBLogger, defaults...)

    tuples = Dict([defaults..., (:sig_deg, 0), (:sel, 0), (:pairs, 0),
                   (:mat, (0,0)), (:density, zero(Float32)), (:arit_ops, 0),
                   (:syz, 0), (:new, 0), (:time, zero(Float64))])
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
                                add_row = false,
                                defaults = [],
                                curr_sort_id = 0,
                                curr_index_hash = 0,
                                interred = false,
                                sig_degree = -1,
                                sugar_deg = -1,
                                min_deg = -1,
                                nselected = 0,
                                npairs = 0,
                                nz_entries = 0,
                                mat_size = (0, 0),
                                indx = 0,
                                indx_hash = 0,
                                tag = nothing,
                                arit_ops = 0,
                                new_syz = false,
                                new_basis = false,
                                gb_or_sat = nothing,
                                gb_size = 0,
                                gb_size_aft_interred = 0,
                                start_time_core = 0.0,
                                end_time_core = 0.0,
                                kwargs...)

    if level == Verbose1
        if curr_sort_id != 0
            println("sort ID $(curr_sort_id), index hash $(curr_index_hash), sig degree $(sig_degree), tag $(tag)")
        end
        if interred
            println("Interreducing...")
        end
        if sugar_deg > -1
            println("current degree $(sugar_deg)")
        end
    elseif level == Verbose2
        if add_row
            add_info_row!(logger, defaults...)
        end
        if !(isnothing(gb_or_sat))
            set_info_row!(logger, (:gb_or_sat, gb_or_sat))
        end
        if sig_degree >= 0
            set_info_row!(logger, (:sig_deg, sig_degree))
        end
        if sugar_deg >= 0
            set_info_row!(logger, (:sugar_deg, sugar_deg))
        end
        if min_deg >= 0
            set_info_row!(logger, (:min_deg, min_deg))
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
        if indx_hash != 0
            set_info_row!(logger, (:indx_hash, indx_hash))
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
            inc_row!(logger, :new)
        end
        if gb_size != 0
            set_info_row!(logger, (:size, gb_size))
        end
        if gb_size_aft_interred != 0
            set_info_row!(logger, (:size_aft, gb_size_aft_interred))
        end
        if start_time_core != 0.0
            logger.stop_watch_start = start_time_core
        end
        if end_time_core != 0.0
            set_info_row!(logger, (:time, round(end_time_core - logger.stop_watch_start, digits = 4)))
            logger.stop_watch_start = 0.0
        end
    end
    # fallback to global logger
    if level >= Logging.min_enabled_level(logger.logger) && !(level in [Verbose1, Verbose2])
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
