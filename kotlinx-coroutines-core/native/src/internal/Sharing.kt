/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.internal

import kotlinx.atomicfu.*
import kotlinx.coroutines.*
import kotlin.coroutines.*
import kotlin.coroutines.intrinsics.*
import kotlin.native.concurrent.*
import kotlin.native.ref.*

internal actual open class ShareableRefHolder {
    internal var shareable: ShareableObject<*>? = null // cached result of asShareable call
}

internal actual fun ShareableRefHolder.disposeSharedRef() {
    shareable?.disposeRef()
}

internal actual fun <T> T.asShareable(): DisposableHandle where T : DisposableHandle, T : ShareableRefHolder {
    shareable?.let { return it as DisposableHandle }
    return ShareableDisposableHandle(this).also { shareable = it }
}

internal actual fun CoroutineDispatcher.asShareable(): CoroutineDispatcher = when (this) {
    is EventLoopImpl -> shareable
    else -> this
}

internal actual fun <T> Continuation<T>.asShareable() : Continuation<T> = when (this) {
    is ShareableContinuation<T> -> this
    else -> ShareableContinuation(this)
}

internal actual fun <T> Continuation<T>.asLocal() : Continuation<T> = when (this) {
    is ShareableContinuation -> localRef()
    else -> this
}

internal actual fun <T> Continuation<T>.asLocalOrNull() : Continuation<T>? = when (this) {
    is ShareableContinuation -> localRefOrNull()
    else -> this
}

internal actual fun <T> Continuation<T>.asLocalOrNullIfNotUsed() : Continuation<T>? = when (this) {
    is ShareableContinuation -> localRefOrNullIfNotUsed()
    else -> this
}

internal actual fun <T> Continuation<T>.useLocal() : Continuation<T> = when (this) {
    is ShareableContinuation -> useRef()
    else -> this
}

internal actual fun <T> Continuation<T>.shareableInterceptedResumeCancellableWith(result: Result<T>) {
    this as ShareableContinuation<T> // must have been shared
    val thread = ownerThreadOrNull ?: wasUsed()
    if (currentThread() == thread) {
        useRef().intercepted().resumeCancellableWith(result)
    } else {
        thread.execute {
            useRef().intercepted().resumeCancellableWith(result)
        }
    }
}

internal actual fun <T> Continuation<T>.shareableInterceptedResumeWith(result: Result<T>) {
    this as ShareableContinuation<T> // must have been shared
    val thread = ownerThreadOrNull ?: wasUsed()
    if (currentThread() == thread) {
        useRef().intercepted().resumeWith(result)
    } else {
        thread.execute {
            useRef().intercepted().resumeWith(result)
        }
    }
}

internal actual fun <T, R> (suspend (T) -> R).asShareable(): suspend (T) -> R =
    ShareableBlock(this)

@PublishedApi
internal actual inline fun disposeContinuation(cont: () -> Continuation<*>) {
    (cont() as ShareableContinuation<*>).disposeRef()
}

internal actual fun <T> CancellableContinuationImpl<T>.shareableResume(delegate: Continuation<T>, undispatched: Boolean) {
    if (delegate is ShareableContinuation) {
        val thread = delegate.ownerThreadOrNull ?: delegate.wasUsed()
        if (currentThread() == thread) {
            resume(delegate.useRef(), undispatched)
        } else {
            thread.execute {
                resume(delegate.useRef(), undispatched)
            }
        }
        return
    }
    resume(delegate, undispatched)
}

internal actual fun isReuseSupportedInPlatform() = false

internal actual inline fun <T> ArrayList<T>.addOrUpdate(element: T, update: (ArrayList<T>) -> Unit) {
    if (isFrozen) {
        val list = ArrayList<T>(size + 1)
        list.addAll(this)
        list.add(element)
        update(list)
    } else {
        add(element)
    }
}

internal actual inline fun <T> ArrayList<T>.addOrUpdate(index: Int, element: T, update: (ArrayList<T>) -> Unit) {
    if (isFrozen) {
        val list = ArrayList<T>(size + 1)
        list.addAll(this)
        list.add(index, element)
        update(list)
    } else {
        add(index, element)
    }
}

@Suppress("NOTHING_TO_INLINE")
internal actual inline fun Any.weakRef(): Any = WeakReference(this)

internal actual fun Any?.unweakRef(): Any? = (this as WeakReference<*>?)?.get()

internal open class ShareableObject<T : Any>(obj: T) {
    private val _ref = atomic<WorkerBoundReference<T>?>(WorkerBoundReference(obj))

    val ownerThreadOrNull: Thread?
        get() = _ref.value?.worker?.toThread()
    
    fun localRef(): T {
        val ref = _ref.value ?: wasUsed()
        return ref.value
    }

    fun localRefOrNull(): T? {
        val ref = _ref.value ?: wasUsed()
        if (Worker.current != ref.worker) return null
        return ref.value
    }

    fun localRefOrNullIfNotUsed(): T? {
        val ref = _ref.value ?: return null
        if (Worker.current != ref.worker) return null
        return ref.value
    }

    fun useRef(): T {
        val ref = _ref.getAndSet(null) ?: wasUsed()
        return ref.value
    }

    fun disposeRef(): T? {
        val ref = _ref.getAndSet(null) ?: return null
        return ref.value
    }

    fun wasUsed(): Nothing {
        error("Ref $classSimpleName@$hexAddress was already used")
    }

    override fun toString(): String {
        val ref = _ref.value ?: return "Shareable[used]"
        return "Shareable[${if (Worker.current == ref.worker) _ref.value.toString() else "wrong worker"}]"
    }
}

@PublishedApi
internal class ShareableContinuation<T>(
    cont: Continuation<T>
) : ShareableObject<Continuation<T>>(cont), Continuation<T> {
    override val context: CoroutineContext = cont.context

    override fun resumeWith(result: Result<T>) {
        val thread = ownerThreadOrNull ?: wasUsed()
        if (currentThread() == thread) {
            useRef().resumeWith(result)
        } else {
            thread.execute {
                useRef().resumeWith(result)
            }
        }
    }
}

private class ShareableDisposableHandle(
    handle: DisposableHandle
) : ShareableObject<DisposableHandle>(handle), DisposableHandle {
    override fun dispose() {
        val thread = ownerThreadOrNull ?: return
        if (currentThread() == thread) {
            disposeRef()?.dispose()
        } else {
            thread.execute {
                disposeRef()?.dispose()
            }
        }
    }
}

private typealias Block1<T, R> = suspend (T) -> R
private typealias Fun2<T, R> = Function2<T, Continuation<R>, Any?>

// todo: SuspendFunction impl is a hack to workaround the absence of proper suspend fun implementation ability
@Suppress("SUPERTYPE_IS_SUSPEND_FUNCTION_TYPE", "INCONSISTENT_TYPE_PARAMETER_VALUES")
private class ShareableBlock<T, R>(
    block: Block1<T, R>
) : ShareableObject<Block1<T, R>>(block), Block1<T, R>, Fun2<T, R> {
    override suspend fun invoke(param: T): R = useRef().invoke(param)

    @Suppress("UNCHECKED_CAST")
    override fun invoke(param: T, cont: Continuation<R>): Any? =
        (useRef() as Fun2<T, R>).invoke(param, cont)
}
