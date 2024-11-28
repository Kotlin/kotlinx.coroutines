package kotlinx.coroutines

import kotlinx.coroutines.flow.flow
import kotlinx.coroutines.flow.flowOn
import kotlinx.coroutines.flow.single
import kotlinx.coroutines.internal.Symbol
import kotlinx.coroutines.internal.commonThreadLocal
import kotlinx.coroutines.testing.TestBase
import kotlin.coroutines.CoroutineContext
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertNotSame

class CommonThreadContextMutableCopiesTest : TestBase() {
    companion object {
        internal val threadLocalData = commonThreadLocal<MutableList<String>>(Symbol("ThreadLocalData"))
    }

    class MyMutableElement(
        val mutableData: MutableList<String>
    ) : CopyableThreadContextElement<MutableList<String>> {

        companion object Key : CoroutineContext.Key<MyMutableElement>

        override val key: CoroutineContext.Key<*>
            get() = Key

        override fun updateThreadContext(context: CoroutineContext): MutableList<String> {
            val st = threadLocalData.get()
            threadLocalData.set(mutableData)
            return st
        }

        override fun restoreThreadContext(context: CoroutineContext, oldState: MutableList<String>) {
            threadLocalData.set(oldState)
        }

        override fun copyForChild(): MyMutableElement {
            return MyMutableElement(ArrayList(mutableData))
        }

        override fun mergeForChild(overwritingElement: CoroutineContext.Element): MyMutableElement {
            overwritingElement as MyMutableElement // <- app-specific, may be another subtype
            return MyMutableElement((mutableData.toSet() + overwritingElement.mutableData).toMutableList())
        }
    }

    @Test
    fun testDataIsCopied() = runTest {
        val root = MyMutableElement(ArrayList())
        launch(root) {
            val data = threadLocalData.get()
            expect(1)
            launch(root) {
                assertNotSame(data, threadLocalData.get())
                assertEquals(data, threadLocalData.get())
                finish(2)
            }
        }
    }

    @Test
    fun testDataIsNotOverwritten() = runTest {
        val root = MyMutableElement(ArrayList())
        withContext(root) {
            expect(1)
            val originalData = threadLocalData.get()
            threadLocalData.get().add("X")
            launch {
                threadLocalData.get().add("Y")
                // Note here, +root overwrites the data
                launch(Dispatchers.Default + root) {
                    assertEquals(listOf("X", "Y"), threadLocalData.get())
                    assertNotSame(originalData, threadLocalData.get())
                    finish(2)
                }
            }
        }
    }

    @Test
    fun testDataIsMerged() = runTest {
        val root = MyMutableElement(ArrayList())
        withContext(root) {
            expect(1)
            val originalData = threadLocalData.get()
            threadLocalData.get().add("X")
            launch {
                threadLocalData.get().add("Y")
                // Note here, +root overwrites the data
                launch(Dispatchers.Default + MyMutableElement(mutableListOf("Z"))) {
                    assertEquals(listOf("X", "Y", "Z"), threadLocalData.get())
                    assertNotSame(originalData, threadLocalData.get())
                    finish(2)
                }
            }
        }
    }

    @Test
    fun testDataIsNotOverwrittenWithContext() = runTest {
        val root = MyMutableElement(ArrayList())
        withContext(root) {
            val originalData = threadLocalData.get()
            threadLocalData.get().add("X")
            expect(1)
            launch {
                threadLocalData.get().add("Y")
                // Note here, +root overwrites the data
                withContext(Dispatchers.Default + root) {
                    assertEquals(listOf("X", "Y"), threadLocalData.get())
                    assertNotSame(originalData, threadLocalData.get())
                    finish(2)
                }
            }
        }
    }

    @Test
    fun testDataIsCopiedForCoroutine() = runTest {
        val root = MyMutableElement(ArrayList())
        val originalData = root.mutableData
        expect(1)
        launch(root) {
            assertNotSame(originalData, threadLocalData.get())
            finish(2)
        }
    }

    @Test
    fun testDataIsCopiedThroughFlowOnUndispatched() = runTest {
        expect(1)
        val root = MyMutableElement(ArrayList())
        val originalData = root.mutableData
        flow {
            assertNotSame(originalData, threadLocalData.get())
            emit(1)
        }
            .flowOn(root)
            .single()
        finish(2)
    }

    @Test
    fun testDataIsCopiedThroughFlowOnDispatched() = runTest {
        expect(1)
        val root = MyMutableElement(ArrayList())
        val originalData = root.mutableData
        flow {
            assertNotSame(originalData, threadLocalData.get())
            emit(1)
        }
            .flowOn(root + Dispatchers.Default)
            .single()
        finish(2)
    }
}