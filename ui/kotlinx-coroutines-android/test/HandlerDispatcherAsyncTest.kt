package kotlinx.coroutines.android

import kotlinx.coroutines.testing.*
import android.os.*
import kotlinx.coroutines.*
import org.junit.Test
import org.junit.runner.*
import org.robolectric.*
import org.robolectric.Shadows.*
import org.robolectric.annotation.*
import org.robolectric.shadows.*
import org.robolectric.util.*
import java.util.concurrent.*
import kotlin.test.*

@RunWith(RobolectricTestRunner::class)
@Config(manifest = Config.NONE, sdk = [28])
@LooperMode(LooperMode.Mode.LEGACY)
class HandlerDispatcherAsyncTest : TestBase() {

    /**
     * Because [Dispatchers.Main] is a singleton, we cannot vary its initialization behavior. As a
     * result we only test its behavior on the newest API level and assert that it uses async
     * messages. We rely on the other tests to exercise the variance of the mechanism that the main
     * dispatcher uses to ensure it has correct behavior on all API levels.
     */
    @Test
    fun mainIsAsync() = runTest {
        ReflectionHelpers.setStaticField(Build.VERSION::class.java, "SDK_INT", 28)

        val mainLooper = shadowOf(Looper.getMainLooper())
        mainLooper.pause()
        val mainMessageQueue = shadowOf(Looper.getMainLooper().queue)

        val job = launch(Dispatchers.Main) {
            expect(2)
        }

        val message = mainMessageQueue.head
        assertTrue(message.isAsynchronous)
        job.join(mainLooper)
    }

    @Test
    fun asyncMessagesApi14() = runTest {
        ReflectionHelpers.setStaticField(Build.VERSION::class.java, "SDK_INT", 14)

        val main = Looper.getMainLooper().asHandler(async = true).asCoroutineDispatcher()

        val mainLooper = shadowOf(Looper.getMainLooper())
        mainLooper.pause()
        val mainMessageQueue = shadowOf(Looper.getMainLooper().queue)

        val job = launch(main) {
            expect(2)
        }

        val message = mainMessageQueue.head
        assertFalse(message.isAsynchronous)
        job.join(mainLooper)
    }

    @Test
    fun asyncMessagesApi16() = runTest {
        ReflectionHelpers.setStaticField(Build.VERSION::class.java, "SDK_INT", 16)

        val main = Looper.getMainLooper().asHandler(async = true).asCoroutineDispatcher()

        val mainLooper = shadowOf(Looper.getMainLooper())
        mainLooper.pause()
        val mainMessageQueue = shadowOf(Looper.getMainLooper().queue)

        val job = launch(main) {
            expect(2)
        }

        val message = mainMessageQueue.head
        assertTrue(message.isAsynchronous)
        job.join(mainLooper)
    }

    @Test
    fun asyncMessagesApi28() = runTest {
        ReflectionHelpers.setStaticField(Build.VERSION::class.java, "SDK_INT", 28)

        val main = Looper.getMainLooper().asHandler(async = true).asCoroutineDispatcher()

        val mainLooper = shadowOf(Looper.getMainLooper())
        mainLooper.pause()
        val mainMessageQueue = shadowOf(Looper.getMainLooper().queue)

        val job = launch(main) {
            expect(2)
        }

        val message = mainMessageQueue.head
        assertTrue(message.isAsynchronous)
        job.join(mainLooper)
    }

    @Test
    fun noAsyncMessagesIfNotRequested() = runTest {
        ReflectionHelpers.setStaticField(Build.VERSION::class.java, "SDK_INT", 28)

        val main = Looper.getMainLooper().asHandler(async = false).asCoroutineDispatcher()

        val mainLooper = shadowOf(Looper.getMainLooper())
        mainLooper.pause()
        val mainMessageQueue = shadowOf(Looper.getMainLooper().queue)

        val job = launch(main) {
            expect(2)
        }

        val message = mainMessageQueue.head
        assertFalse(message.isAsynchronous)
        job.join(mainLooper)
    }

    @Test
    fun testToString() {
        ReflectionHelpers.setStaticField(Build.VERSION::class.java, "SDK_INT", 28)
        val main = Looper.getMainLooper().asHandler(async = true).asCoroutineDispatcher("testName")
        assertEquals("testName", main.toString())
        assertEquals("testName.immediate", main.immediate.toString())
        assertEquals("testName.immediate", main.immediate.immediate.toString())
    }

    private suspend fun Job.join(mainLooper: ShadowLooper) {
        expect(1)
        mainLooper.unPause()
        join()
        finish(3)
    }

    // TODO compile against API 23+ so this can be invoked without reflection.
    private val Looper.queue: MessageQueue
        get() = Looper::class.java.getDeclaredMethod("getQueue").invoke(this) as MessageQueue

    // TODO compile against API 22+ so this can be invoked without reflection.
    private val Message.isAsynchronous: Boolean
        get() = Message::class.java.getDeclaredMethod("isAsynchronous").invoke(this) as Boolean
}
