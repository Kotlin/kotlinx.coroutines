package kotlinx.coroutines

import kotlinx.coroutines.testing.*
import kotlin.test.*

class UndispatchedWithContextTest : TestBase() {
    
    @Test
    fun testWithContextGuaranteesCorrectDispatcher() = runBlocking {
        val mainThread = Thread.currentThread()
        expect(1)
        
        suspend fun doSomeIo(): String = withContext(Dispatchers.IO) {
            assertNotSame(mainThread, Thread.currentThread(), "Code should run on IO dispatcher, not main thread")
            expect(3)
            "OK"
        }
        
        val ioScope = CoroutineScope(Dispatchers.IO + SupervisorJob())
        
        ioScope.launch(start = CoroutineStart.UNDISPATCHED) {
            expect(2)
            val result = doSomeIo()
            expect(4)
            assertEquals("OK", result)
        }.join()
        
        finish(5)
    }
}
