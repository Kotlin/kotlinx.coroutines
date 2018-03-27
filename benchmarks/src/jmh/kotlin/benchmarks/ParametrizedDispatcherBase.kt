package benchmarks

import benchmarks.actors.CORES_COUNT
import kotlinx.coroutines.experimental.CommonPool
import kotlinx.coroutines.experimental.ThreadPoolDispatcher
import kotlinx.coroutines.experimental.newFixedThreadPoolContext
import kotlinx.coroutines.experimental.scheduling.ExperimentalCoroutineDispatcher
import org.openjdk.jmh.annotations.Param
import org.openjdk.jmh.annotations.Setup
import org.openjdk.jmh.annotations.TearDown
import java.io.Closeable
import kotlin.coroutines.experimental.CoroutineContext

/**
 * Base class to use different [CoroutineContext] in benchmarks via [Param] in inheritors.
 * Currently allowed values are "fjp" for [CommonPool] and ftp_n for [ThreadPoolDispatcher] with n threads.
 */
abstract class ParametrizedDispatcherBase {

    abstract var dispatcher: String
    lateinit var benchmarkContext: CoroutineContext // coroutinesContext clashes with scope parameter
    var closeable: Closeable? = null

    @Setup
    open fun setup() {
        benchmarkContext = when {
            dispatcher == "fjp" -> CommonPool
            dispatcher == "experimental" -> {
                ExperimentalCoroutineDispatcher(CORES_COUNT)
            }
            dispatcher.startsWith("ftp") -> {
                newFixedThreadPoolContext(dispatcher.substring(4).toInt(), dispatcher).also { closeable = it }
            }
            else -> error("Unexpected dispatcher: $dispatcher")
        }
    }

    @TearDown
    fun tearDown() {
        closeable?.close()
    }

}