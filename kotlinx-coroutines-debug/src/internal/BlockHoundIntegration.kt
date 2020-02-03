package kotlinx.coroutines.debug.internal

import reactor.blockhound.BlockHound
import kotlin.reflect.KClass
import kotlin.reflect.full.*

internal object BlockHoundIntegration {

    init {
        val cls = Class.forName("kotlinx.coroutines.scheduling.CoroutineScheduler\$Worker").kotlin
        initializerHelper(cls)
    }

    private fun <T : Any> initializerHelper(cls: KClass<T>) {
        val field = cls.declaredMemberProperties.find { it.name == "state" }!!
        BlockHound.builder()
                .addDynamicThreadPredicate(cls::isInstance)
                .nonBlockingThreadPredicate { p ->
                    p.or { thread ->
                        val castThread = cls.safeCast(thread)
                        if (!enabled || castThread == null) {
                            false
                        } else {
                            val state = field(castThread) as Enum<*>
                            state.name == "CPU_ACQUIRED"
                        }
                    }
                }
                .install()
    }

    @Volatile
    private var enabled = false

    fun install() {
        enabled = true
    }

    fun uninstall() {
        enabled = false
    }

}
