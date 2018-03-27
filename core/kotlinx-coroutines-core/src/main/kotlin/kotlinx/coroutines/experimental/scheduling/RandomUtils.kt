package kotlinx.coroutines.experimental.scheduling

import java.util.*

private val RANDOM = object : ThreadLocal<Random>() {
    override fun initialValue() = Random()
}

// Dynamic discovery is not yet supported
val RANDOM_PROVIDER = { RANDOM.get() }
