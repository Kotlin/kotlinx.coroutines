/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

import org.junit.rules.*
import org.junit.runner.*
import org.junit.runners.model.*
import java.util.concurrent.*
import kotlin.coroutines.*

class ExecutorRule(private val numberOfThreads: Int) : TestRule, ExecutorCoroutineDispatcher() {

    private var _executor: ExecutorCoroutineDispatcher? = null
    override val executor: Executor
        get() = _executor?.executor ?: error("Executor is not initialized")

    override fun apply(base: Statement, description: Description): Statement {
        return object : Statement() {
            override fun evaluate() {
                val threadPrefix = description.className.substringAfterLast(".") + "#" + description.methodName
                _executor = newFixedThreadPoolContext(numberOfThreads, threadPrefix)
                ignoreLostThreads(threadPrefix)
                try {
                    return base.evaluate()
                } finally {
                    val service = executor as ExecutorService
                    service.shutdown()
                    if (!service.awaitTermination(10, TimeUnit.SECONDS)) {
                        error("Test $description timed out")
                    }
                }
            }
        }
    }

    override fun dispatch(context: CoroutineContext, block: Runnable) {
        _executor?.dispatch(context, block) ?: error("Executor is not initialized")
    }

    override fun close() {
        error("Cannot be closed manually")
    }
}
