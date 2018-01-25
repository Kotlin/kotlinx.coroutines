package kotlinx.coroutines.debug.agent

import kotlinx.coroutines.debug.manager.*
import kotlinx.coroutines.debug.manager.StackChangedEvent.*
import kotlinx.coroutines.debug.transformer.CoroutinesDebugTransformer
import sun.misc.Signal
import java.io.FileOutputStream
import java.lang.instrument.Instrumentation
import java.lang.management.ManagementFactory

class Agent {
    companion object {
        @JvmStatic
        fun premain(agentArgs: String?, inst: Instrumentation) {
            agentSetup(agentArgs, inst)
            info { "called Agent.premain($agentArgs, $inst)" }
        }

        @JvmStatic
        fun agentmain(agentArgs: String?, inst: Instrumentation) {
            agentSetup(agentArgs, inst)
            info { "called Agent.agentmain($agentArgs, $inst)" }
        }

        private fun agentSetup(agentArgs: String?, inst: Instrumentation) {
            tryConfigureLogger(agentArgs)
            System.setProperty("kotlinx.coroutines.debug", "")
            addSignalHandler(agentArgs)
            if (Logger.config.dataConsumers.isNotEmpty()) {
                StacksManager.addOnStackChangedCallback { event, coroutineContext ->
                    if (event == Created || event == Suspended || event == Removed)
                        data {
                            buildString {
                                append("event: $event for context $coroutineContext\n")
                                append("snapshot:\n")
                                append(getSnapshot().prettyPrint())
                            }
                        }
                }
            }
            inst.addTransformer(CoroutinesDebugTransformer())
        }
    }
}

private fun addSignalHandler(agentArgs: String?) { //FIXME?
    val signalValue = agentArgs?.split(',')?.find { it.toLowerCase().startsWith("signal=") }?.split('=')?.get(1)
    val signal = signalValue?.let {
        try {
            Signal(it.toUpperCase())
        } catch (e: Exception) {
            error { "Unknown signal name '$signalValue' in agent arguments" }
            null
        }
    } ?: Signal("USR2")
    Signal.handle(signal, {
        val coroutineDump = StacksManager.getSnapshot().fullCoroutineDump(Configuration.Run)
        System.err.println(coroutineDump.toString())
    })
    val pid = with(ManagementFactory.getRuntimeMXBean().name) { substring(0, indexOf('@')) }
    info { "Add ${signal.name}(${signal.number}) signal handler, my pid is $pid" }
}

private fun tryConfigureLogger(agentArgs: String?) {
    val EVENTS_DEBUG_LOG_FILE = "all-events.debug.log"
    val logLevel = agentArgs?.split(',')?.find { it.toLowerCase().startsWith("loglevel=") }
            ?.split('=')?.get(1)?.let { value ->
        try {
            LogLevel.valueOf(value.toUpperCase())
        } catch (e: IllegalArgumentException) {
            error { "Unknown log level '$value' in agent arguments" }
            LogLevel.INFO
        }
    } ?: LogLevel.INFO
    val logFileOutputStream = agentArgs?.split(',')?.find { it.toLowerCase().startsWith("logfile=") }
            ?.split('=')?.get(1)?.let { FileOutputStream(it) }
    val dataFileOutputStream = if (logLevel <= LogLevel.DEBUG) FileOutputStream(EVENTS_DEBUG_LOG_FILE) else null
    Logger.config = logFileOutputStream?.let {
        logToFile(logLevel, withTime = true, logFileOutputStream = logFileOutputStream,
                dataConsumers = listOfNotNull(dataFileOutputStream))
    } ?: LoggerConfig(logLevel, withTime = true, dataConsumers = listOfNotNull(dataFileOutputStream))
}

