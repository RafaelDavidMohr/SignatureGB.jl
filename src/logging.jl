using Logging

const Verbose1 = Logging.LogLevel(-1250)
const Verbose2 = Logging.LogLevel(-1750)

mutable struct SGBLogger{L <: AbstractLogger} <: AbstractLogger
    logger::L
    verbose_level::Int
    # TODO: data to record
end

# TODO: put in initial data, based on sigpolynomialctx
function SGBLogger(args...; verbose = 0)
    if iszero(verbose)
        return SGBLogger(global_logger(), Logging.LogLevel(0), args...)
    elseif isone(verbose)
        return SGBLogger(global_logger(), Verbose1, args...)
    elseif verbose == 2
        return SGBLogger(global_logger(), Verbose2, args...)
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
end
            
function Logging.shouldlog(logger::SGBLogger, level, args...)
    level in [Verbose1, Verbose2] && return true
    Logging.shouldlog(logger.logger, args...)
end

Logging.min_enabled_level(logger::SGBLogger) = minimum(logger.logger.level, logger.verbose_level)

function Logging.catch_exceptions(logger::SGBLogger)
    Logging.catch_exceptions(logger.logger)
end
