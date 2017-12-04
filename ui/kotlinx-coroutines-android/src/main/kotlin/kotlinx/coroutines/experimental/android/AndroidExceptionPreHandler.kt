package kotlinx.coroutines.experimental.android

import kotlinx.coroutines.experimental.CoroutineExceptionHandler
import java.lang.reflect.Modifier
import kotlin.coroutines.experimental.AbstractCoroutineContextElement
import kotlin.coroutines.experimental.CoroutineContext

private val getter =
    try {
        Thread::class.java.getDeclaredMethod("getUncaughtExceptionPreHandler").takeIf {
            Modifier.isPublic(it.modifiers) && Modifier.isStatic(it.modifiers)
        }
    }
    catch (e: Throwable) { null /* not found */ }

/**
 * Uses Android's `Thread.getUncaughtExceptionPreHandler()` whose default behavior is to log exception.
 * See
 * [here](https://github.com/aosp-mirror/platform_frameworks_base/blob/2efbc7239f419c931784acf98960ed6abc38c3f2/core/java/com/android/internal/os/RuntimeInit.java#L142)
 *
 * @suppress This is an internal impl class.
 */
class AndroidExceptionPreHandler :
    AbstractCoroutineContextElement(CoroutineExceptionHandler), CoroutineExceptionHandler
{
    override fun handleException(context: CoroutineContext, exception: Throwable) {
        (getter?.invoke(null) as? Thread.UncaughtExceptionHandler)
            ?.uncaughtException(Thread.currentThread(), exception)
    }
}