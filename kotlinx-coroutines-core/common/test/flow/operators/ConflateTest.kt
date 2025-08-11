package kotlinx.coroutines.flow

import kotlinx.coroutines.*
import kotlinx.coroutines.testing.*
import kotlin.test.*

class ConflateTest : TestBase() {
    @Test // from example
    fun testExample() = withVirtualTime {
        expect(1)
        val flow = flow {
            for (i in 1..30) {
                delay(100)
                emit(i)
            }
        }
        val result = flow.conflate().onEach {
            delay(1000)
        }.toList()
        assertEquals(listOf(1, 10, 20, 30), result)
        finish(2)
    }


//    @Test
//    fun testDispatched() = withVirtualTime {
//        expect(1)
//        val flow = flow {
//            for (i in 1..30) {
//                delay(10)
//                emit(i)
//            }
//        }
//        val result = flow.flowOn(wrapperDispatcher()).conflate().onEach {
//            println("Emitting $it")  // prints 1 once and hangs  // todo: ask Dmitry
//            delay(100)
//        }.toList()
//        assertEquals(listOf(1, 10, 20, 30), result)
//        finish(2)
//    }
}
