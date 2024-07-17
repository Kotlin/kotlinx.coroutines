@file:Suppress("unused")
package kotlinx.coroutines.lincheck

import kotlinx.coroutines.testing.*
import kotlinx.coroutines.*
import kotlinx.coroutines.sync.*
import org.jetbrains.kotlinx.lincheck.*
import org.jetbrains.kotlinx.lincheck.annotations.Operation
import org.jetbrains.kotlinx.lincheck.strategy.managed.modelchecking.*

abstract class SemaphoreLincheckTestBase(permits: Int) : AbstractLincheckTest() {
    private val semaphore = SemaphoreAndMutexImpl(permits = permits, acquiredPermits = 0)

    @Operation
    fun tryAcquire() = semaphore.tryAcquire()

    @Operation(promptCancellation = true, allowExtraSuspension = true)
    suspend fun acquire() = semaphore.acquire()

    @Operation(handleExceptionsAsResult = [IllegalStateException::class])
    fun release() = semaphore.release()

    override fun <O : Options<O, *>> O.customize(isStressTest: Boolean): O =
        actorsBefore(0)

    override fun ModelCheckingOptions.customize(isStressTest: Boolean) =
        checkObstructionFreedom()
}

class Semaphore1LincheckTest : SemaphoreLincheckTestBase(1)
class Semaphore2LincheckTest : SemaphoreLincheckTestBase(2)
