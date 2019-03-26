/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines


import com.esotericsoftware.kryo.*
import com.esotericsoftware.kryo.io.*
import kotlinx.atomicfu.*
import org.junit.Test
import org.objenesis.strategy.*
import java.io.*
import kotlin.coroutines.*
import kotlin.coroutines.intrinsics.*
import kotlin.reflect.*
import kotlin.test.*

@Ignore
class ContinuationSerializationTest : TestBase() {

    companion object {
        @JvmStatic
        var flag = false
    }

//    private val atomicInt = atomic(1)

    private val kryo =
        Kryo().also { it.instantiatorStrategy = Kryo.DefaultInstantiatorStrategy(StdInstantiatorStrategy()) }

    private var storage: ByteArrayOutputStream = ByteArrayOutputStream()

    @Test
    fun testSafeContinuationSerDe() = testSerization(::serialize, {
        it.javaClass.getDeclaredField("result").apply {
            isAccessible = true
            set(it, COROUTINE_SUSPENDED)
        }
    })

    @Test
    fun testUnsafeContinuationSerDe() = testSerization(::serializeUnsafe, {})

//    @Test
//    fun testCancellableContinuationSerDe() = testSerization(::serializeCancellable, {
//        it.javaClass.superclass.getDeclaredField("_decision").apply {
//            isAccessible = true
//            set(it, atomicInt)
//        }
//    })

    private suspend fun serialize() = suspendCoroutine<Unit> { cont ->
        Output(storage).use {
            kryo.writeClassAndObject(it, cont)
        }
    }

    private suspend fun serializeCancellable() = suspendCancellableCoroutine<Unit> { cont ->
        Output(storage).use {
            kryo.writeClassAndObject(it, cont)
        }
    }

    private suspend fun serializeUnsafe() = suspendCoroutineUninterceptedOrReturn<Unit> { cont ->
        Output(storage).use {
            kryo.writeClassAndObject(it, cont)
        }
    }

    private fun testSerization(serialize: KSuspendFunction0<Unit>, patcher: (Continuation<Unit>) -> Unit) =
        runBlocking {
            launch(Unconfined) {
                expect(1)
                serialize()
                flag = true
            }

            val cont = deserialise()
            patcher(cont)
            expect(2)
            cont.resume(Unit)
            finish(3)
            assertTrue(flag)
        }

    @Suppress("UNCHECKED_CAST")
    private fun deserialise(): Continuation<Unit> {
        val input = Input(ByteArrayInputStream(storage.toByteArray()))
        input.use {
            return kryo.readClassAndObject(it) as Continuation<Unit>
        }
    }
}
