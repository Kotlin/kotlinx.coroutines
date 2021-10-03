/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.internal

import kotlinx.coroutines.*
import java.util.*
import kotlin.coroutines.*

/**
 * Name of the boolean property that enables using of [FastServiceLoader].
 */
private const val FAST_SERVICE_LOADER_PROPERTY_NAME = "kotlinx.coroutines.fast.service.loader"

// Lazy loader for the main dispatcher
internal object MainDispatcherLoader {

    private val FAST_SERVICE_LOADER_ENABLED = systemProp(FAST_SERVICE_LOADER_PROPERTY_NAME, true)

    @JvmField
    val dispatcher: MainCoroutineDispatcher = loadMainDispatcher()

    private fun loadMainDispatcher(): MainCoroutineDispatcher {
        return try {
            val factories = if (FAST_SERVICE_LOADER_ENABLED) {
                FastServiceLoader.loadMainDispatcherFactory()
            } else {
                // We are explicitly using the
                // `ServiceLoader.load(MyClass::class.java, MyClass::class.java.classLoader).iterator()`
                // form of the ServiceLoader call to enable R8 optimization when compiled on Android.
                ServiceLoader.load(
                        MainDispatcherFactory::class.java,
                        MainDispatcherFactory::class.java.classLoader
                ).iterator().asSequence().toList()
            }
            @Suppress("ConstantConditionIf")
            factories.maxByOrNull { it.loadPriority }?.tryCreateDispatcher(factories)
                ?: createMissingDispatcher()
        } catch (e: Throwable) {
            // Service loader can throw an exception as well
            createMissingDispatcher(e)
        }
    }
}

/**
 * If anything goes wrong while trying to create main dispatcher (class not found,
 * initialization failed, etc), then replace the main dispatcher with a special
 * stub that throws an error message on any attempt to actually use it.
 *
 * @suppress internal API
 */
@InternalCoroutinesApi
public fun MainDispatcherFactory.tryCreateDispatcher(factories: List<MainDispatcherFactory>): MainCoroutineDispatcher =
    try {
        createDispatcher(factories)
    } catch (cause: Throwable) {
        createMissingDispatcher(cause, hintOnError())
    }

/** @suppress */
@InternalCoroutinesApi
public fun MainCoroutineDispatcher.isMissing(): Boolean = this is MissingMainCoroutineDispatcher

// R8 optimization hook, not const on purpose to enable R8 optimizations via "assumenosideeffects"
@Suppress("MayBeConstant")
private val SUPPORT_MISSING = true

@Suppress(
    "ConstantConditionIf",
    "IMPLICIT_NOTHING_TYPE_ARGUMENT_AGAINST_NOT_NOTHING_EXPECTED_TYPE" // KT-47626
)
private fun createMissingDispatcher(cause: Throwable? = null, errorHint: String? = null) =
    if (SUPPORT_MISSING) MissingMainCoroutineDispatcher(cause, errorHint) else
        cause?.let { throw it } ?: throwMissingMainDispatcherException()

internal fun throwMissingMainDispatcherException(): Nothing {
    throw IllegalStateException(
        "Module with the Main dispatcher is missing. " +
            "Add dependency providing the Main dispatcher, e.g. 'kotlinx-coroutines-android' " +
            "and ensure it has the same version as 'kotlinx-coroutines-core'"
    )
}

private class MissingMainCoroutineDispatcher(
    private val cause: Throwable?,
    private val errorHint: String? = null
) : MainCoroutineDispatcher(), Delay {

    override val immediate: MainCoroutineDispatcher get() = this

    override fun isDispatchNeeded(context: CoroutineContext): Boolean =
        missing()

    override suspend fun delay(time: Long) =
        missing()

    override fun invokeOnTimeout(timeMillis: Long, block: Runnable, context: CoroutineContext): DisposableHandle =
        missing()

    override fun dispatch(context: CoroutineContext, block: Runnable) =
        missing()

    override fun scheduleResumeAfterDelay(timeMillis: Long, continuation: CancellableContinuation<Unit>) =
        missing()

    private fun missing(): Nothing {
        if  (cause == null) {
            throwMissingMainDispatcherException()
        } else {
            val message = "Module with the Main dispatcher had failed to initialize" + (errorHint?.let { ". $it" } ?: "")
            throw IllegalStateException(message, cause)
        }
    }

    override fun toString(): String = "Dispatchers.Main[missing${if (cause != null) ", cause=$cause" else ""}]"
}

/**
 * @suppress
 */
@InternalCoroutinesApi
public object MissingMainCoroutineDispatcherFactory : MainDispatcherFactory {
    override val loadPriority: Int
        get() = -1

    override fun createDispatcher(allFactories: List<MainDispatcherFactory>): MainCoroutineDispatcher {
        return MissingMainCoroutineDispatcher(null)
    }
}
