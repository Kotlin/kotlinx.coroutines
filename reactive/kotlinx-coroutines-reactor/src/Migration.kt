@file:JvmName("FlowKt")

package kotlinx.coroutines.reactor

import kotlinx.coroutines.flow.*
import reactor.core.publisher.*

/** @suppress **/
@Deprecated(
    message = "Replaced in favor of ReactiveFlow extension, please import kotlinx.coroutines.reactor.* instead of kotlinx.coroutines.reactor.FlowKt",
    level = DeprecationLevel.HIDDEN
) // Compatibility with Spring 5.2-RC
@JvmName("asFlux")
public fun <T : Any> Flow<T>.asFluxDeprecated(): Flux<T> = asFlux()
