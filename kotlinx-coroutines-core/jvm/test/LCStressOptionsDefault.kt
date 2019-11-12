/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */
package kotlinx.coroutines

import org.jetbrains.kotlinx.lincheck.*
import org.jetbrains.kotlinx.lincheck.strategy.stress.*
import kotlin.reflect.*

class LCStressOptionsDefault : StressOptions() {
    init {
        iterations(100 * stressTestMultiplierCbrt)
        invocationsPerIteration(1000 * stressTestMultiplierCbrt)
        actorsBefore(if (isStressTest) 3 else 0)
        threads(3)
        actorsPerThread(if (isStressTest) 3 else 2)
    }
}

fun Options<*,*>.check(testClass: KClass<*>) = LinChecker.check(testClass.java, this)