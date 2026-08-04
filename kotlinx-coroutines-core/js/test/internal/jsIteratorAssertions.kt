package kotlinx.coroutines.internal

import kotlinx.coroutines.await
import kotlin.test.assertEquals

internal suspend fun <T> assertNextStepToBe(
    iterator: JsAsyncIterator<T>,
    value: T? = js("undefined"),
    done: Boolean = false
) {
    val result = iterator.next().await()
    assertEquals(done, result.done)
    assertEquals(value, result.value)
}
