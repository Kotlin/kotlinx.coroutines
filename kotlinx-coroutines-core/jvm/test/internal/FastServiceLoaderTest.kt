package kotlinx.coroutines.internal

import kotlinx.coroutines.*
import kotlin.test.*

class FastServiceLoaderTest : TestBase() {
    @Test
    fun testCrossModuleService() {
        val providers = CoroutineScope::class.java.let { FastServiceLoader.loadProviders(it, it.classLoader) }
        assertEquals(3, providers.size)
        val className = "kotlinx.coroutines.android.EmptyCoroutineScopeImpl"
        for (i in 1 .. 3) {
            assert(providers[i - 1].javaClass.name == "$className$i")
        }
    }
}
