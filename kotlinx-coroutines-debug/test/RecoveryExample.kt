@file:Suppress("PackageDirectoryMismatch")
package example

import kotlinx.coroutines.*

object PublicApiImplementation : CoroutineScope by CoroutineScope(CoroutineName("Example")) {

    private fun doWork(): Int {
        error("Internal invariant failed")
    }

    private fun asynchronousWork(): Int {
        return doWork() + 1
    }

    public suspend fun awaitAsynchronousWorkInMainThread() {
        val task = async(Dispatchers.Default) {
            asynchronousWork()
        }

        task.await()
    }
}

suspend fun main() {
    // Try to switch debug mode on and off to see the difference
    PublicApiImplementation.awaitAsynchronousWorkInMainThread()
}
