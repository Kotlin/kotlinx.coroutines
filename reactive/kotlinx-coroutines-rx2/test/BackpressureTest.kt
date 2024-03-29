package kotlinx.coroutines.rx2

import kotlinx.coroutines.testing.*
import io.reactivex.*
import kotlinx.coroutines.*
import kotlinx.coroutines.flow.*
import kotlinx.coroutines.reactive.*
import org.junit.Test
import kotlin.test.*

class BackpressureTest : TestBase() {
    @Test
    fun testBackpressureDropDirect() = runTest {
        expect(1)
        Flowable.fromArray(1)
            .onBackpressureDrop()
            .collect {
                assertEquals(1, it)
                expect(2)
            }
        finish(3)
    }

    @Test
    fun testBackpressureDropFlow() = runTest {
        expect(1)
        Flowable.fromArray(1)
            .onBackpressureDrop()
            .asFlow()
            .collect {
                assertEquals(1, it)
                expect(2)
            }
        finish(3)
    }
}