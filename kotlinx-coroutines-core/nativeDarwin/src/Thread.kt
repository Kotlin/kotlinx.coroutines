/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

import kotlinx.atomicfu.*
import kotlinx.cinterop.*
import platform.CoreFoundation.*
import platform.darwin.*
import kotlin.native.concurrent.*

/**
 * Initializes the main thread. Must be called from the main thread if the application's interaction
 * with Kotlin runtime and coroutines API otherwise starts from background threads.
 */
@ExperimentalCoroutinesApi
public fun initMainThread() {
    getOrCreateMainThread()
}

internal actual fun initCurrentThread(): Thread =
    if (isMainThread()) mainThread else WorkerThread()

internal actual fun Worker.toThread(): Thread =
    if (this == mainThread.worker) mainThread else WorkerThread(this)

@SharedImmutable
private val _mainThread = AtomicReference<MainThread?>(null)

internal val mainThread: MainThread get() = _mainThread.value ?: getOrCreateMainThread()

private fun getOrCreateMainThread(): MainThread {
    require(isMainThread()) {
        "Coroutines must be initialized from the main thread: call 'initMainThread' from the main thread first"
    }
    _mainThread.value?.let { return it }
    return MainThread().also { _mainThread.value = it }
}

internal class MainThread : WorkerThread() {
    private val posted = atomic(false)

    private val processQueueBlock: dispatch_block_t =  {
        posted.value = false // next execute will post a fresh task
        while (worker.processQueue()) { /* process all */ }
    }

    init { freeze() }

    override fun execute(block: () -> Unit) {
        super.execute(block)
        // post to main queue if needed
        if (posted.compareAndSet(false, true)) {
            dispatch_async(dispatch_get_main_queue(), processQueueBlock)
        }
    }

    fun shutdown() {
        // Cleanup posted processQueueBlock
        execute {
            CFRunLoopStop(CFRunLoopGetCurrent())
        }
        CFRunLoopRun()
        assert(!posted.value) // nothing else should have been posted
    }

    override fun toString(): String = "MainThread"
}
