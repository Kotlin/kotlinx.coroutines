/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.experimental

import org.junit.*
import org.junit.Assert.*
import java.lang.reflect.*
import java.util.concurrent.*

class CommonPoolTest {
    private inline fun <T> Try(block: () -> T) = try { block() } catch (e: Throwable) { null }

    @Test
    fun testIsGoodCommonPool() {
        // Test only on JDKs that has all we need
        val fjpClass = Try { Class.forName("java.util.concurrent.ForkJoinPool") } ?: return
        val wtfClass = Try { Class.forName("java.util.concurrent.ForkJoinPool${'$'}ForkJoinWorkerThreadFactory") } ?: return
        val dwtfClass = Try { Class.forName("java.util.concurrent.ForkJoinPool${'$'}DefaultForkJoinWorkerThreadFactory") } ?: return
        // We need private constructor to create "broken" FJP instance
        val fjpCtor = Try { fjpClass.getDeclaredConstructor(
            Int::class.java,
            wtfClass,
            Thread.UncaughtExceptionHandler::class.java,
            Int::class.java,
            String::class.java
        ) } ?: return
        fjpCtor.isAccessible = true
        val dwtfCtor = Try { dwtfClass.getDeclaredConstructor() } ?: return
        dwtfCtor.isAccessible = true
        // Create bad pool
        val fjp0: ExecutorService = createFJP(0, fjpCtor, dwtfCtor) ?: return
        assertFalse(CommonPool.isGoodCommonPool(fjpClass, fjp0))
        fjp0.shutdown()
        // Create good pool
        val fjp1: ExecutorService = createFJP(1, fjpCtor, dwtfCtor) ?: return
        assertTrue(CommonPool.isGoodCommonPool(fjpClass, fjp1))
        fjp1.shutdown()
        println("CommonPool.isGoodCommonPool test passed")
    }

    fun createFJP(
        parallelism: Int,
        fjpCtor: Constructor<out Any>,
        dwtfCtor: Constructor<out Any>
    ): ExecutorService? = Try {
        fjpCtor.newInstance(
            parallelism,
            dwtfCtor.newInstance(),
            Thread.getDefaultUncaughtExceptionHandler(),
            0,
            "Worker"
        )
    } as? ExecutorService
}