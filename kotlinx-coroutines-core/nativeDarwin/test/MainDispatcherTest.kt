package kotlinx.coroutines

import kotlinx.coroutines.testing.*
import kotlinx.cinterop.*
import kotlinx.coroutines.testing.*
import platform.CoreFoundation.*
import platform.darwin.*
import kotlin.coroutines.*
import kotlin.test.*

class MainDispatcherTest : MainDispatcherTestBase.WithRealTimeDelay() {

    override fun isMainThread(): Boolean = CFRunLoopGetCurrent() == CFRunLoopGetMain()

    // skip if already on the main thread, run blocking doesn't really work well with that
    override fun shouldSkipTesting(): Boolean = isMainThread()

    override fun scheduleOnMainQueue(block: () -> Unit) {
        autoreleasepool {
            dispatch_async(dispatch_get_main_queue()) {
                block()
            }
        }
    }
}
