/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package benchmarks

import benchmarks.akka.CORES_COUNT
import kotlinx.coroutines.*
import kotlinx.coroutines.scheduling.*
import org.openjdk.jmh.annotations.Param
import org.openjdk.jmh.annotations.Setup
import org.openjdk.jmh.annotations.TearDown
import java.io.Closeable
import java.util.concurrent.*
import kotlin.coroutines.CoroutineContext

/**
 * Base class to use different [CoroutineContext] in benchmarks via [Param] in inheritors.
 * Currently allowed values are "fjp" for [CommonPool] and ftp_n for [ThreadPoolDispatcher] with n threads.
 */
abstract class ParametrizedDispatcherBase : CoroutineScope {

    abstract var dispatcher: String
    override lateinit var coroutineContext: CoroutineContext
    private var closeable: Closeable? = null

    @Setup
    open fun setup() {
        coroutineContext = when {
            dispatcher == "fjp" -> ForkJoinPool.commonPool().asCoroutineDispatcher()
            dispatcher == "scheduler" -> {
                Dispatchers.Default
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
