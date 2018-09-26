/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.experimental.slf4j

import com.codahale.metrics.MetricRegistry
import kotlinx.coroutines.experimental.TestBase
import kotlinx.coroutines.experimental.metrics.newInstrumentedFixedThreadPoolContext
import kotlinx.coroutines.experimental.metrics.newInstrumentedSingleThreadContext
import kotlinx.coroutines.experimental.runBlocking
import org.junit.Test

class InstrumentedCoroutineDispatchersTest : TestBase() {
    private fun checkThreadName(prefix: String) {
        val name = Thread.currentThread().name
        check(name.startsWith(prefix)) { "Expected thread name to start with '$prefix', found: '$name'" }
    }

    @Test
    fun testSingleThread() {
        val metricRegistry = MetricRegistry()
        val context = newInstrumentedSingleThreadContext("TestThread", metricRegistry)
        runBlocking(context) {
            checkThreadName("TestThread")
        }
        context.close()
    }

    @Test
    fun testFixedThreadPool() {
        val metricRegistry = MetricRegistry()
        val context = newInstrumentedFixedThreadPoolContext(2, "TestPool", metricRegistry)
        runBlocking(context) {
            checkThreadName("TestPool")
        }
        context.close()
    }
}