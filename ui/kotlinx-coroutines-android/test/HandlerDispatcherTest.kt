/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.experimental.android

import android.os.Build
import android.os.Looper
import android.os.Message
import android.os.MessageQueue
import kotlinx.coroutines.experimental.Dispatchers
import kotlinx.coroutines.experimental.GlobalScope
import kotlinx.coroutines.experimental.launch
import org.junit.Test
import org.junit.runner.RunWith
import org.robolectric.RobolectricTestRunner
import org.robolectric.Shadows.shadowOf
import org.robolectric.annotation.Config
import org.robolectric.shadows.ShadowLooper
import org.robolectric.util.ReflectionHelpers
import kotlin.test.assertFalse
import kotlin.test.assertTrue

@RunWith(RobolectricTestRunner::class)
@Config(manifest = Config.NONE, sdk = [28])
class HandlerDispatcherTest {

  /**
   * Because [Dispatchers.Main] is a singleton, we cannot vary its initialization behavior. As a
   * result we only test its behavior on the newest API level and assert that it uses async
   * messages. We rely on the other tests to exercise the variance of the mechanism that the main
   * dispatcher uses to ensure it has correct behavior on all API levels.
   */
  @Test fun mainIsAsync() {
    ReflectionHelpers.setStaticField(Build.VERSION::class.java, "SDK_INT", 28)

    val mainLooper = ShadowLooper.getShadowMainLooper()
    mainLooper.pause()
    val mainMessageQueue = shadowOf(Looper.getMainLooper().queue)

    val job = GlobalScope.launch(Dispatchers.Main) {}

    val message = mainMessageQueue.head
    assertTrue(message.isAsynchronous)

    job.cancel()
  }

  @Test fun asyncMessagesApi14() {
    ReflectionHelpers.setStaticField(Build.VERSION::class.java, "SDK_INT", 14)

    val main = Looper.getMainLooper().asHandler(async = true).asCoroutineDispatcher()

    val mainLooper = ShadowLooper.getShadowMainLooper()
    mainLooper.pause()
    val mainMessageQueue = shadowOf(Looper.getMainLooper().queue)

    val job = GlobalScope.launch(main) {}

    val message = mainMessageQueue.head
    assertFalse(message.isAsynchronous)

    job.cancel()
  }

  @Test fun asyncMessagesApi16() {
    ReflectionHelpers.setStaticField(Build.VERSION::class.java, "SDK_INT", 16)

    val main = Looper.getMainLooper().asHandler(async = true).asCoroutineDispatcher()

    val mainLooper = ShadowLooper.getShadowMainLooper()
    mainLooper.pause()
    val mainMessageQueue = shadowOf(Looper.getMainLooper().queue)

    val job = GlobalScope.launch(main) {}

    val message = mainMessageQueue.head
    assertTrue(message.isAsynchronous)

    job.cancel()
  }

  @Test fun asyncMessagesApi28() {
    ReflectionHelpers.setStaticField(Build.VERSION::class.java, "SDK_INT", 28)

    val main = Looper.getMainLooper().asHandler(async = true).asCoroutineDispatcher()

    val mainLooper = ShadowLooper.getShadowMainLooper()
    mainLooper.pause()
    val mainMessageQueue = shadowOf(Looper.getMainLooper().queue)

    val job = GlobalScope.launch(main) {}

    val message = mainMessageQueue.head
    assertTrue(message.isAsynchronous)

    job.cancel()
  }

  @Test fun noAsyncMessagesIfNotRequested() {
    ReflectionHelpers.setStaticField(Build.VERSION::class.java, "SDK_INT", 28)

    val main = Looper.getMainLooper().asHandler(async = false).asCoroutineDispatcher()

    val mainLooper = ShadowLooper.getShadowMainLooper()
    mainLooper.pause()
    val mainMessageQueue = shadowOf(Looper.getMainLooper().queue)

    val job = GlobalScope.launch(main) {}

    val message = mainMessageQueue.head
    assertFalse(message.isAsynchronous)

    job.cancel()
  }

  // TODO compile against API 23+ so this can be invoked without reflection.
  private val Looper.queue: MessageQueue
    get() = Looper::class.java.getDeclaredMethod("getQueue").invoke(this) as MessageQueue

  // TODO compile against API 22+ so this can be invoked without reflection.
  private val Message.isAsynchronous: Boolean
    get() = Message::class.java.getDeclaredMethod("isAsynchronous").invoke(this) as Boolean
}
