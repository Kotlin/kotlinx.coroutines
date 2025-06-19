@file:Suppress("unused")

package kotlinx.coroutines.lincheck

import kotlinx.coroutines.*
import kotlinx.coroutines.internal.*
import org.jetbrains.lincheck.datastructures.*
import org.jetbrains.lincheck.datastructures.verifier.QuiescentConsistencyVerifier
import org.jetbrains.lincheck.datastructures.verifier.QuiescentConsistent

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
