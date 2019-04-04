package kotlinx.coroutines.internal

import kotlinx.coroutines.CoroutineScope
import kotlinx.coroutines.Delay
import kotlin.test.*

class FastServiceLoaderTest {
    @Test
    fun testLoadingSameModuleService() {
        val providers = Delay::class.java.let { FastServiceLoader.loadProviders(it, it.classLoader) }
        assertEquals(1, providers.size)
        assertEquals("kotlinx.coroutines.android.DelayImpl", providers[0].javaClass.name)
    }

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