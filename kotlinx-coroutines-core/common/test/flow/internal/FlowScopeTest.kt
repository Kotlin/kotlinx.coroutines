package kotlinx.coroutines.flow.internal

import kotlinx.coroutines.testing.*
import kotlinx.coroutines.*
import kotlin.test.*

class FlowScopeTest : TestBase() {

    @Test
    fun testCancellation() = runTest {
        assertFailsWith<CancellationException> {
            flowScope {
                expect(1)
                val child = launch {
                    expect(3)
                    hang { expect(5) }
                }
                expect(2)
                yield()
                expect(4)
                child.cancel()
            }
        }
        finish(6)
    }

    @Test
    fun testCancellationWithChildCancelled() = runTest {
        flowScope {
            expect(1)
            val child = launch {
                expect(3)
                hang { expect(5) }
            }
            expect(2)
            yield()
            expect(4)
            child.cancel(ChildCancelledException())
        }
        finish(6)
    }

    @Test
    fun testCancellationWithSuspensionPoint() = runTest {
        assertFailsWith<CancellationException> {
            flowScope {
                expect(1)
                val child = launch {
                    expect(3)
                    hang { expect(6) }
                }
                expect(2)
                yield()
                expect(4)
                child.cancel()
                hang { expect(5) }
            }
        }
        finish(7)
    }

    @Test
    fun testNestedScopes() = runTest {
        assertFailsWith<CancellationException> {
            flowScope {
                flowScope {
                    launch {
                       throw CancellationException("")
                    }
                }
            }
        }
    }
}
