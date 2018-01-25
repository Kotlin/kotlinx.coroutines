package kotlinx.coroutines.debug.test

import org.junit.Assert
import org.junit.Test

class CoroutineMatcherDSLTest {
    private val suspendFoo = "\"foo#1\" [...]\n" +
            "  Status: Suspended at kotlinx.coroutines.experimental.DelayKt.delay\n" +
            "    at kotlinx.coroutines.experimental.DelayKt.delay\$default(Delay.kt:85)\n" +
            "    at MainKt.testInner(Main.kt:48)\n" +
            "    at MainKt.test(Main.kt:43)\n" +
            "    at MainKt\$main\$1.invoke(Main.kt:53)"

    private val MAIN_THREAD = "Thread[main,5,main]"

    private val LAUNCH_INFRASTRUCTURE =
            "    at kotlin.coroutines.experimental.jvm.internal.CoroutineImpl.resume(CoroutineImpl.kt:54)\n" +
                    "    at kotlinx.coroutines.experimental.DispatchedContinuation.resume(CoroutineDispatcher.kt:223)\n" +
                    "    at kotlin.coroutines.experimental.CoroutinesKt.startCoroutine(CoroutinesLibrary.kt:35)"

    private val runningFoo = "\"foo#2\"\n" +
            "  Status: Running on $MAIN_THREAD\n" +
            "    at coroutine.foo.whatever(Foo.kt:42)\n" +
            "    at coroutine.foo.other(Foo.kt:37)\n" +
            "    -- ^^ foo#2 (current) ^^\n" +
            LAUNCH_INFRASTRUCTURE

    private val runningFooBar = "\"foo#2\" [foo(2), ..., Unconfined]\n" +
            "  Status: Running on $MAIN_THREAD\n" +
            "    at coroutine.foo.whatever(Foo.kt:42)\n" +
            "    at coroutine.foo.other(Foo.kt:37)\n" +
            "    -- ^^ foo#2 (current) ^^\n" +
            LAUNCH_INFRASTRUCTURE + "\n" +
            "    at coroutine.bar.blah\$1.launchFoo(Bar.kt:50)\n" +
            "    at coroutine.bar.blah\$1.invoke(Bar.kt:30)\n" +
            "    -- ^^ bar#1 ^^\n" +
            LAUNCH_INFRASTRUCTURE + "\n" +
            "    at plane.kotlin.call(Main.kt:10)"

    private val createdFoo = "" //TODO

    //suspend OK
    @Test
    fun testSuspendFullStack() {
        val matcher = coroutine("foo#1", Suspended("kotlinx.coroutines.experimental.DelayKt.delay")) {
            method("kotlinx.coroutines.experimental.DelayKt.delay\$default", "Delay.kt", 85)
            method("MainKt.testInner")
            method("MainKt.test")
            method("MainKt\$main\$1.invoke")
        }
        suspendMatcherOK(matcher)
    }

    @Test
    fun testSuspendZeroOrMore() {
        val matcher = coroutine("foo#1", Suspended("kotlinx.coroutines.experimental.DelayKt.delay")) {
            zeroOrMore("wrong.position")
            zeroOrMore("kotlinx.coroutines.experimental.DelayKt.delay\$default", "WrongFile")
            3.methods(any)
            method("MainKt\$main\$1.invoke", "Main.kt", 53)
        }
        suspendMatcherOK(matcher)
    }

    @Test
    fun testSuspendOneOrMore() {
        val matcher = coroutine("foo#1", Suspended("kotlinx.coroutines.experimental.DelayKt.delay")) {
            oneOrMore("kotlinx.coroutines.experimental.DelayKt.delay\$default", "Delay.kt", 85)
            2.methods(any)
            method("MainKt\$main\$1.invoke", "Main.kt", 53)
        }
        suspendMatcherOK(matcher)
    }

    @Test
    fun testSuspendTimes() {
        val matcher = coroutine("foo#1", Suspended("kotlinx.coroutines.experimental.DelayKt.delay")) {
            method("kotlinx.coroutines.experimental.DelayKt.delay\$default", "Delay.kt", 85)
            1.methods("MainKt.testInner", "Main.kt")
            2.methods(any)
        }
        suspendMatcherOK(matcher)
    }

    //suspend should fail
    @Test
    fun testSuspendWrongNameDoesntMatch() {
        val matcher = coroutine("Wrong Name", Suspended("kotlinx.coroutines.experimental.DelayKt.delay")) {
            method("kotlinx.coroutines.experimental.DelayKt.delay\$default", "Delay.kt", 85)
            method("MainKt.testInner")
            method("MainKt.test")
            method("MainKt\$main\$1.invoke")
        }
        suspendMatcherFAIL(matcher)
    }

    @Test
    fun testWrongLineNumberDoesntMatch() {
        val matcher = coroutine("foo#1", Suspended("kotlinx.coroutines.experimental.DelayKt.delay")) {
            method("kotlinx.coroutines.experimental.DelayKt.delay\$default", "Delay.kt", 42)
            3.methods(any)
        }
        suspendMatcherFAIL(matcher)
    }

    @Test
    fun testWrongFileDoesntMatch() {
        val matcher = coroutine("foo#1", Suspended("kotlinx.coroutines.experimental.DelayKt.delay")) {
            method("kotlinx.coroutines.experimental.DelayKt.delay\$default", "WrongFile", 85)
            3.methods(any)
        }
        suspendMatcherFAIL(matcher)
    }

    @Test
    fun testSuspendWrongSuspendAtDoesntMatch() {
        val matcher = coroutine("foo#1", Suspended("wrong.position")) {
            method("kotlinx.coroutines.experimental.DelayKt.delay\$default", "Delay.kt", 85)
            method("MainKt.testInner")
            method("MainKt.test")
            method("MainKt\$main\$1.invoke")
        }
        suspendMatcherFAIL(matcher)
    }

    @Test
    fun testSuspendPartDoesntMatch() {
        val matcher = coroutine("foo#1", Suspended("kotlinx.coroutines.experimental.DelayKt.delay")) {
            method("kotlinx.coroutines.experimental.DelayKt.delay\$default", "Delay.kt", 85)
            method("MainKt.testInner")
        }
        suspendMatcherFAIL(matcher)
    }

    @Test
    fun testSuspendWrongOneOrMoreDoesntMatch() {
        val matcherOK = coroutine("foo#1", Suspended("kotlinx.coroutines.experimental.DelayKt.delay")) {
            zeroOrMore("wrong.method")
            zeroOrMore(any)
        }
        suspendMatcherOK(matcherOK)
        val matcherFail = coroutine("foo#1", Suspended("kotlinx.coroutines.experimental.DelayKt.delay")) {
            oneOrMore("wrong.method")
            zeroOrMore(any)
        }
        suspendMatcherFAIL(matcherFail)
    }

    @Test
    fun testWrongStateDoesntMatch() {
        val matcher = coroutine("foo#1", Running()) {
            method("kotlinx.coroutines.experimental.DelayKt.delay\$default", "Delay.kt", 85)
            method("MainKt.testInner")
            method("MainKt.test")
            method("MainKt\$main\$1.invoke")
        }
        suspendMatcherFAIL(matcher)
    }

    @Test
    fun testEmptyStackDoesntMatch() {
        val matcher = coroutine("foo#1", Running()) {
        }
        suspendMatcherFAIL(matcher)
    }

    //running Foo OK
    @Test
    fun testRunningFooIgnoreThread() {
        val matcher = coroutine("foo#2", Running()) {
            method("coroutine.foo.whatever", "Foo.kt", 42)
            method("coroutine.foo.other", "Foo.kt", 37)
            marker("foo#2", true)
            3.methods(any) //infrastructure
        }
        runningFooMatcherOK(matcher)
    }

    @Test
    fun testRunningFooCheckThread() {
        val matcher = coroutine("foo#2", Running()) {
            method("coroutine.foo.whatever", "Foo.kt", 42)
            method("coroutine.foo.other", "Foo.kt", 37)
            marker("foo#2", true)
            3.methods(any) //infrastructure
        }
        runningFooMatcherOK(matcher)
    }

    @Test
    fun testRunningFooAnyMarkerAny() {
        val matcher = coroutine("foo#2", Running()) {
            oneOrMore(any)
            marker("foo#2", true)
            3.methods(any) //infrastructure
        }
        runningFooMatcherOK(matcher)
    }

    //running Foo should fail
    @Test
    fun testRunningFooWrongInfrastructureDoesntMatch() {
        val matcher = coroutine("foo#2", Running()) {
            method("coroutine.foo.whatever", "Foo.kt", 42)
            method("coroutine.foo.other", "Foo.kt", 37)
            marker("foo#2", true)
            method(any)
            method("coroutine.foo.whatever", "Foo.kt", 42)
            method(any)
        }
        runningFooMatcherFAIL(matcher)
    }

    @Test
    fun testRunningFooWrongThreadDoesntMatch() {
        val matcher = coroutine("foo#2", Running("Wrong thread")) {
            method("coroutine.foo.whatever", "Foo.kt", 42)
            method("coroutine.foo.other", "Foo.kt", 37)
            marker("foo#2", true)
            3.methods(any) //infrastructure
        }
        runningFooMatcherFAIL(matcher)
    }

    @Test
    fun testRunningFooWrongMarkerDoesntMatch() {
        val matcher = coroutine("foo#2", Running()) {
            method("coroutine.foo.whatever", "Foo.kt", 42)
            method("coroutine.foo.other", "Foo.kt", 37)
            marker("wrong marker", true)
            3.methods(any) //infrastructure
        }
        runningFooMatcherFAIL(matcher)
    }

    @Test
    fun testRunningFooWrongMarkerDoesntMatch2() {
        val matcher = coroutine("foo#2", Running()) {
            method("coroutine.foo.whatever", "Foo.kt", 42)
            marker("foo#2", true)
            method("coroutine.foo.other", "Foo.kt", 37)
            3.methods(any) //infrastructure
        }
        runningFooMatcherFAIL(matcher)
    }

    @Test
    fun testRunningFooTooManyMarkerDoesntMatch() {
        val matcher = coroutine("foo#2", Running()) {
            method("coroutine.foo.whatever", "Foo.kt", 42)
            method("coroutine.foo.other", "Foo.kt", 37)
            marker("foo#2", true)
            marker("foo#2", true)
            3.methods(any) //infrastructure
        }
        runningFooMatcherFAIL(matcher)
    }

    @Test
    fun testRunningFooWithoutMarkerDoesntMatch() {
        val matcher = coroutine("foo#2", Running()) {
            method("coroutine.foo.whatever", "Foo.kt", 42)
            method("coroutine.foo.other", "Foo.kt", 37)
            3.methods(any) //infrastructure
        }
        runningFooMatcherFAIL(matcher)
    }

    //running Foo Bar OK
    @Test
    fun testRunningFooBarOK1() {
        val matcher = coroutine("foo#2", Running()) {
            zeroOrMore(any)
            marker("foo#2", true)
            zeroOrMore(any)
            marker("bar#1")
            zeroOrMore(any)
        }
        runningFooBarMatcherOK(matcher)
    }

    @Test
    fun testRunningFooBarOK2() {
        val matcher = coroutine("foo#2", Running()) {
            2.methods(any)
            marker("foo#2", true)
            3.methods(any) //infrastructure
            2.methods(any) //coroutine bar#1
            marker("bar#1")
            3.methods(any) //infrastructure
            method(any)
        }
        runningFooBarMatcherOK(matcher)
    }

    @Test
    fun testRunningFooBarOK3() {
        val matcher = coroutine("foo#2", Running()) {
            method("coroutine.foo.whatever", "Foo.kt", 42)
            method("coroutine.foo.other", "Foo.kt", 37)
            marker("foo#2", true)
            3.methods(any) //infrastructure
            method("coroutine.bar.blah\$1.launchFoo", "Bar.kt", 50)
            method("coroutine.bar.blah\$1.invoke", "Bar.kt", 30)
            marker("bar#1")
            3.methods(any) //infrastructure
            method("plane.kotlin.call", "Main.kt", 10)
        }
        runningFooBarMatcherOK(matcher)
    }

    //running Foo Bar Should Fail
    @Test
    fun testRunningFooBarFail1() {
        val matcher = coroutine("foo#2", Running()) {
            method("coroutine.foo.whatever", "Foo.kt", 42)
            method("coroutine.foo.other", "Foo.kt", 37)
            marker("foo#2", true)
            3.methods(any) //infrastructure
            method("coroutine.bar.blah\$1.launchFoo", "Bar.kt", 50)
            method("coroutine.bar.blah\$1.invoke", "Bar.kt", 30)
            marker("bar#1")
            2.methods(any) //should be 3.methods(any)
            method("plane.kotlin.call", "Main.kt", 10)
        }
        runningFooBarMatcherFAIL(matcher)
    }

    @Test
    fun testRunningFooBarWrongSelfMarkerDoesntMatch() {
        val matcher = coroutine("foo#2", Running()) {
            method("coroutine.foo.whatever", "Foo.kt", 42)
            method("coroutine.foo.other", "Foo.kt", 37)
            marker("foo#2")
            3.methods(any) //infrastructure
            method("coroutine.bar.blah\$1.launchFoo", "Bar.kt", 50)
            method("coroutine.bar.blah\$1.invoke", "Bar.kt", 30)
            marker("bar#1", true)
            3.methods(any) //infrastructure
            method("plane.kotlin.call", "Main.kt", 10)
        }
        runningFooBarMatcherFAIL(matcher)
    }

    @Test
    fun testRunningFooBarTwoSelfMarkersDoesntMatch() {
        val matcher = coroutine("foo#2", Running()) {
            method("coroutine.foo.whatever", "Foo.kt", 42)
            method("coroutine.foo.other", "Foo.kt", 37)
            marker("foo#2", true)
            3.methods(any) //infrastructure
            method("coroutine.bar.blah\$1.launchFoo", "Bar.kt", 50)
            method("coroutine.bar.blah\$1.invoke", "Bar.kt", 30)
            marker("bar#1", true)
            3.methods(any) //infrastructure
            method("plane.kotlin.call", "Main.kt", 10)
        }
        runningFooBarMatcherFAIL(matcher)
    }

    @Test
    fun testRunningFooBarFlippedMarkersDoesntMatch() {
        val matcher = coroutine("foo#2", Running()) {
            method("coroutine.foo.whatever", "Foo.kt", 42)
            method("coroutine.foo.other", "Foo.kt", 37)
            marker("bar#1", true)
            3.methods(any) //infrastructure
            method("coroutine.bar.blah\$1.launchFoo", "Bar.kt", 50)
            method("coroutine.bar.blah\$1.invoke", "Bar.kt", 30)
            marker("foo#2")
            3.methods(any) //infrastructure
            method("plane.kotlin.call", "Main.kt", 10)
        }
        runningFooBarMatcherFAIL(matcher)
    }

    private fun suspendMatcherOK(matcher: Coroutine) = Assert.assertTrue(matcher.matchEntireString(suspendFoo))
    private fun suspendMatcherFAIL(matcher: Coroutine) = Assert.assertFalse(matcher.matchEntireString(suspendFoo))


    private fun runningFooMatcherOK(matcher: Coroutine) = Assert.assertTrue(matcher.matchEntireString(runningFoo))
    private fun runningFooMatcherFAIL(matcher: Coroutine) = Assert.assertFalse(matcher.matchEntireString(runningFoo))

    private fun runningFooBarMatcherOK(matcher: Coroutine) = Assert.assertTrue(matcher.matchEntireString(runningFooBar))
    private fun runningFooBarMatcherFAIL(matcher: Coroutine) = Assert.assertFalse(matcher.matchEntireString(runningFooBar))
}