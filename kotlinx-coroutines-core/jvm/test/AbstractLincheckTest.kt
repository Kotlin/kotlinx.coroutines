/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */
package kotlinx.coroutines

import org.jetbrains.kotlinx.lincheck.*
import org.jetbrains.kotlinx.lincheck.strategy.managed.modelchecking.*
import org.jetbrains.kotlinx.lincheck.strategy.stress.*
import org.jetbrains.kotlinx.lincheck.verifier.*
import org.junit.*

abstract class AbstractLincheckTest : VerifierState() {
    open fun <O: Options<O, *>> O.customize(isStressTest: Boolean): O = this
    open fun ModelCheckingOptions.customize(isStressTest: Boolean): ModelCheckingOptions = this
    open fun StressOptions.customize(isStressTest: Boolean): StressOptions = this

    @Test
    open fun modelCheckingTest() = ModelCheckingOptions()
        .iterations(if (isStressTest) 100 else 20)
        .invocationsPerIteration(if (isStressTest) 10_000 else 1_000)
        .commonConfiguration()
        .customize(isStressTest)
        .check(this::class)

    @Test
    fun stressTest() = StressOptions()
        .iterations(if (isStressTest) 100 else 20)
        .invocationsPerIteration(if (isStressTest) 10_000 else 1_000)
        .commonConfiguration()
        .customize(isStressTest)
        .check(this::class)

    private fun <O : Options<O, *>> O.commonConfiguration(): O = this
        .actorsBefore(if (isStressTest) 3 else 1)
        .threads(3)
        .actorsPerThread(if (isStressTest) 4 else 2)
        .actorsAfter(if (isStressTest) 3 else 0)
        .customize(isStressTest)

    override fun extractState(): Any = error("Not implemented")
}
