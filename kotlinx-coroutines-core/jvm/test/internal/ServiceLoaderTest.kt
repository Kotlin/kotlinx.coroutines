package kotlinx.coroutines.internal

import kotlinx.coroutines.CoroutineScope
import kotlinx.coroutines.Delay
import kotlin.test.Test

class ServiceLoaderTest {
    @Test
    fun testLoadingSameModuleService() {
        val providers = Delay::class.java.let { FastServiceLoader.loadProviders(it, it.classLoader) }
        assert(providers.size == 1 && providers[0].javaClass.name == "kotlinx.coroutines.android.DelayImpl")
    }

    @Test
    fun testCrossModuleService() {
        val providers = CoroutineScope::class.java.let { FastServiceLoader.loadProviders(it, it.classLoader) }
        assert(providers.size == 3)
        val className = "kotlinx.coroutines.android.EmptyCoroutineScopeImpl"
        for (i in 1 .. 3) {
            assert(providers[i - 1].javaClass.name == "$className$i")
        }
    }
}