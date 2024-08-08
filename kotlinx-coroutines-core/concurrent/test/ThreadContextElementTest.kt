package kotlinx.coroutines

import kotlinx.coroutines.testing.*
import kotlin.test.*

class ThreadContextElementTest : TestBase() {
    @Test
    fun testWithContext() = runTest {
        expect(1)
        newSingleThreadContext("withContext").use {
            val data = MyData()
            GlobalScope.async(Dispatchers.Default + MyElement(data)) {
                assertSame(data, threadContextElementThreadLocal.get())
                expect(2)

                val newData = MyData()
                GlobalScope.async(it + MyElement(newData)) {
                    assertSame(newData, threadContextElementThreadLocal.get())
                    expect(3)
                }.await()

                withContext(it + MyElement(newData)) {
                    assertSame(newData, threadContextElementThreadLocal.get())
                    expect(4)
                }

                GlobalScope.async(it) {
                    assertNull(threadContextElementThreadLocal.get())
                    expect(5)
                }.await()

                expect(6)
            }.await()
        }

        finish(7)
    }

    @Test
    fun testNonCopyableElementReferenceInheritedOnLaunch() = runTest {
        var parentElement: MyElement? = null
        var inheritedElement: MyElement? = null

        newSingleThreadContext("withContext").use {
            withContext(it + MyElement(MyData())) {
                parentElement = coroutineContext[MyElement.Key]
                launch {
                    inheritedElement = coroutineContext[MyElement.Key]
                }
            }
        }

        assertSame(
            inheritedElement, parentElement,
            "Inner and outer coroutines did not have the same object reference to a" +
                " ThreadContextElement that did not override `copyForChildCoroutine()`"
        )
    }
}
