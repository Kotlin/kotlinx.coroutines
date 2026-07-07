package kotlinx.coroutines

import kotlinx.coroutines.testing.*
import kotlin.test.*

/**
 * [asCoroutineDispatcher] and [awaitAnimationFrame] both require a real `window`: `requestAnimationFrame`,
 * `postMessage` and the rest of the [WindowDispatcher] / [WindowMessageQueue] machinery they rely on don't
 * exist under Node.js or d8. [tryGetTestWindow] returns `null` in those environments, and every test below
 * finishes immediately without asserting anything when that happens, rather than failing outside a browser.
 */
class WindowTest : TestBase() {
    @Test
    fun testDispatch() = runTest {
        val window = tryGetTestWindow()
        if (window == null) {
            finish(1)
        } else {
            launch(window.asCoroutineDispatcher()) {
                expect(1)
                launch {
                    expect(3)
                }
                expect(2)
                yield()
                expect(4)
            }.join()
            finish(5)
        }
    }

    @Test
    fun testDispatcherIsCachedPerWindow() {
        val window = tryGetTestWindow() ?: return
        // asCoroutineDispatcher() must return the same WindowDispatcher on every call for the same window:
        // WindowMessageQueue registers a "message" event listener from its init block, so a fresh instance
        // on every call would leak a listener each time.
        assertSame(window.asCoroutineDispatcher(), window.asCoroutineDispatcher())
    }

    @Test
    fun testAnimationFrameBatching() = runTest {
        val window = tryGetTestWindow()
        if (window == null) {
            finish(1)
        } else {
            expect(1)
            // Both calls are issued before control returns to the browser, so they must be batched into
            // the same requestAnimationFrame callback and resume with an identical timestamp.
            coroutineScope {
                val first = async { window.awaitAnimationFrame() }
                val second = async { window.awaitAnimationFrame() }
                assertEquals(first.await(), second.await())
            }
            finish(2)
        }
    }

    @Test
    fun testAnimationFrameChainedCallLandsInNextFrame() = runTest {
        val window = tryGetTestWindow()
        if (window == null) {
            finish(1)
        } else {
            expect(1)
            // Requesting a new frame from inside an already-resumed callback must not be batched into the
            // frame that's currently resuming it, but scheduled for the one after.
            val firstFrame = window.awaitAnimationFrame()
            val secondFrame = window.awaitAnimationFrame()
            assertTrue(secondFrame > firstFrame)
            finish(2)
        }
    }
}

/** Returns a real, usable `window`, or `null` in environments that don't have one (Node.js, d8). */
internal expect fun tryGetTestWindow(): W3CWindow?
