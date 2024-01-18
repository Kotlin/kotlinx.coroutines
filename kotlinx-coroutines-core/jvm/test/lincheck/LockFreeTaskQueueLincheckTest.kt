@file:Suppress("unused")

package kotlinx.coroutines.lincheck

import kotlinx.coroutines.*
import kotlinx.coroutines.internal.*
import org.jetbrains.kotlinx.lincheck.*
import org.jetbrains.kotlinx.lincheck.annotations.*
import org.jetbrains.kotlinx.lincheck.annotations.Operation
import org.jetbrains.kotlinx.lincheck.paramgen.*
import org.jetbrains.kotlinx.lincheck.strategy.managed.modelchecking.*
import org.jetbrains.kotlinx.lincheck.verifier.quiescent.*

@Param(name = "value", gen = IntGen::class, conf = "1:3")
internal abstract class AbstractLockFreeTaskQueueWithoutRemoveLincheckTest(
    val singleConsumer: Boolean
) : AbstractLincheckTest() {
    @JvmField
    protected val q = LockFreeTaskQueue<Int>(singleConsumer = singleConsumer)

    @Operation
    fun close() = q.close()

    @Operation
    fun addLast(@Param(name = "value") value: Int) = q.addLast(value)

    override fun <O : Options<O, *>> O.customize(isStressTest: Boolean): O =
        verifier(QuiescentConsistencyVerifier::class.java)

    override fun ModelCheckingOptions.customize(isStressTest: Boolean) =
        checkObstructionFreedom()
}

internal class MCLockFreeTaskQueueWithRemoveLincheckTest : AbstractLockFreeTaskQueueWithoutRemoveLincheckTest(singleConsumer = false) {
    @QuiescentConsistent
    @Operation(blocking = true)
    fun removeFirstOrNull() = q.removeFirstOrNull()
}

internal class SCLockFreeTaskQueueWithRemoveLincheckTest : AbstractLockFreeTaskQueueWithoutRemoveLincheckTest(singleConsumer = true) {
    @QuiescentConsistent
    @Operation(nonParallelGroup = "consumer")
    fun removeFirstOrNull() = q.removeFirstOrNull()
}