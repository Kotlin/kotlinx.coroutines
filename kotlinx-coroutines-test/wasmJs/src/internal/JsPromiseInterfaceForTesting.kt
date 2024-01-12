/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.test.internal

/* This is a declaration of JS's `Promise<Unit>`. We need to keep it a separate class, because
`actual typealias TestResult = Promise<Unit>` fails: you can't instantiate an `expect class` with a typealias to
a parametric class. So, we make a non-parametric class just for this. */
/**
 * @suppress
 */
@JsName("Promise")
public external class JsPromiseInterfaceForTesting {
    /**
     * @suppress
     */
    public fun then(onFulfilled: ((JsAny) -> Unit), onRejected: ((JsAny) -> Unit)): JsPromiseInterfaceForTesting
    /**
     * @suppress
     */
    public fun then(onFulfilled: ((JsAny) -> Unit)): JsPromiseInterfaceForTesting
}
