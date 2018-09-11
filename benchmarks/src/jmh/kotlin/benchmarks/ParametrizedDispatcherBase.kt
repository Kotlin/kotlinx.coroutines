/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package benchmarks

import benchmarks.actors.CORES_COUNT
import kotlinx.coroutines.experimental.*
import kotlinx.coroutines.experimental.scheduling.*
import org.openjdk.jmh.annotations.Param
import org.openjdk.jmh.annotations.Setup
import org.openjdk.jmh.annotations.TearDown
import java.io.Closeable
import kotlin.coroutines.experimental.CoroutineContext

/**
 * Base class to use different [CoroutineContext] in benchmarks via [Param] in inheritors.
 * Currently allowed values are "fjp" for [CommonPool] and ftp_n for [ThreadPoolDispatcher] with n threads.
 */
abstract class ParametrizedDispatcherBase : CoroutineScope {

    abstract var dispatcher: String
    override lateinit var coroutineContext: CoroutineContext
    var closeable: Closeable? = null

    @Setup
    open fun setup() {
        coroutineContext = when {
            dispatcher == "fjp" -> CommonPool
            dispatcher == "experimental" -> {
                ExperimentalCoroutineDispatcher(CORES_COUNT).also { closeable = it }
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