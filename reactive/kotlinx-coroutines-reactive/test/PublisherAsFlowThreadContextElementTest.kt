package kotlinx.coroutines.reactive

import kotlinx.coroutines.*
import kotlinx.coroutines.flow.*
import kotlinx.coroutines.testing.*
import org.reactivestreams.*
import kotlin.coroutines.*
import kotlin.test.*

class PublisherAsFlowThreadContextElementTest: TestBase() {
    val threadLocal = ThreadLocal<String>.withInitial { "default" }

    @Test
    fun testFlowOnThreadContext() = runBlocking {
        val publisher = Publisher<Int> { it ->
            it.onSubscribe(object : Subscription {
                override fun request(n: Long) {
                    assertEquals("value", threadLocal.get())
                    it.onNext(1)
                    it.onComplete()
                }

                override fun cancel() {}
            })
        }

        val context1 = Dispatchers.IO + threadLocal.asContextElement("value")
        val context2 = threadLocal.asContextElement("value")

        // succeeds
        publisher.asFlow().flowOn(context1).collect { }
        // fails with org.junit.ComparisonFailure: expected:<[value]> but was:<[default]>
        publisher.asFlow().flowOn(context2).collect { }
    }

    @Test
    fun testDataIsCopiedThroughFlowOnUndispatched() = runTest {
        val originalData = mutableListOf("X")
        val root = MyMutableElement(originalData)
        Publisher<Int> { it ->
            it.onSubscribe(object : Subscription {
                override fun request(n: Long) {
                    val threadLocalData = threadLocalData.get()
                    assertNotSame(originalData, threadLocalData)
                    assertEquals(originalData, threadLocalData)
                    it.onNext(1)
                    it.onComplete()
                }

                override fun cancel() {}
            })
        }.asFlow()
            .flowOn(root)
            .single()
    }

    @Test
    fun testDataIsCopiedThroughFlowOnDispatched() = runTest {
        val originalData = mutableListOf("X")
        val root = MyMutableElement(originalData)
        Publisher<Int> { it ->
            it.onSubscribe(object : Subscription {
                override fun request(n: Long) {
                    val threadLocalData = threadLocalData.get()
                    assertNotSame(originalData, threadLocalData)
                    assertEquals(originalData, threadLocalData)
                    it.onNext(1)
                    it.onComplete()
                }

                override fun cancel() {}
            })
        }.asFlow()
            .flowOn(root + Dispatchers.Default)
            .single()
    }
    
        @Test
    fun testThreadLocalFlowOn() = runTest {
        val parameters: List<Triple<CoroutineContext, Boolean, Boolean>> =
            listOf(EmptyCoroutineContext, Dispatchers.Default, Dispatchers.Unconfined).flatMap { dispatcher ->
                listOf(true, false).flatMap { doYield ->
                    listOf(true, false).map { useThreadLocalInOuterContext ->
                        Triple(dispatcher, doYield, useThreadLocalInOuterContext)
                    }
                }
            }
        for ((dispatcher, doYield, useThreadLocalInOuterContext) in parameters) {
            try {
                testThreadLocalFlowOn(dispatcher, doYield, useThreadLocalInOuterContext)
            } catch (e: Throwable) {
                throw AssertionError("Failed with parameters: dispatcher=$dispatcher, " +
                    "doYield=$doYield, " +
                    "useThreadLocalInOuterContext=$useThreadLocalInOuterContext", e)
            }
        }
    }

    private fun testThreadLocalFlowOn(
        extraFlowOnContext: CoroutineContext, doYield: Boolean, useThreadLocalInOuterContext: Boolean
    ) = runTest {
        try {
            val myData1 = MyData()
            val myData2 = MyData()
            myThreadLocal.set(myData1)
            withContext(if (useThreadLocalInOuterContext) myThreadLocal.asContextElement() else EmptyCoroutineContext) {
                assertEquals(myData1, myThreadLocal.get())
                flow {
                    repeat(5) {
                        assertEquals(myData2, myThreadLocal.get())
                        emit(1)
                        if (doYield) yield()
                    }
                }
                    .flowOn(myThreadLocal.asContextElement(myData2) + extraFlowOnContext)
                    .collect {
                        if (useThreadLocalInOuterContext) {
                            assertEquals(myData1, myThreadLocal.get())
                        }
                    }
                assertEquals(myData1, myThreadLocal.get())
            }
            assertEquals(myData1, myThreadLocal.get())
        } finally {
            myThreadLocal.set(null)
        }
    }

    companion object {
        val threadLocalData: ThreadLocal<MutableList<String>> = ThreadLocal.withInitial { ArrayList() }
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
}

class MyData

// declare thread local variable holding MyData
private val myThreadLocal = ThreadLocal<MyData?>()

// declare context element holding MyData
class MyElement(val data: MyData) : ThreadContextElement<MyData?> {
    // declare companion object for a key of this element in coroutine context
    companion object Key : CoroutineContext.Key<MyElement>

    // provide the key of the corresponding context element
    override val key: CoroutineContext.Key<MyElement>
        get() = Key

    // this is invoked before coroutine is resumed on current thread
    override fun updateThreadContext(context: CoroutineContext): MyData? {
        val oldState = myThreadLocal.get()
        myThreadLocal.set(data)
        return oldState
    }

    // this is invoked after coroutine has suspended on current thread
    override fun restoreThreadContext(context: CoroutineContext, oldState: MyData?) {
        myThreadLocal.set(oldState)
    }
}
