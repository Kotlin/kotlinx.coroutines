/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */
package kotlin.coroutines

// DOKKA STUB
public interface ContinuationInterceptor : CoroutineContext.Element {
    companion object Key : CoroutineContext.Key<ContinuationInterceptor>
    public fun <T> interceptContinuation(continuation: Continuation<T>): Continuation<T>
    public fun releaseInterceptedContinuation(continuation: Continuation<*>): Continuation<*> {
        return continuation
    }
    public override operator fun <E : CoroutineContext.Element> get(key: CoroutineContext.Key<E>): E? = TODO()
    public override fun minusKey(key: CoroutineContext.Key<*>): CoroutineContext = TODO()
}
