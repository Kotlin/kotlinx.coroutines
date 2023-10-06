/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

import kotlinx.coroutines.internal.*

// fixme replace the suppress with AllowDifferentMembersInActual once stdlib is updated to 1.9.20 https://github.com/Kotlin/kotlinx.coroutines/issues/3846
// New 'CompletionHandler` supertype is added compared to the expect declaration.
// Probably we can add it to JS and common too, to avoid the suppression/opt-in
@Suppress("ACTUAL_CLASSIFIER_MUST_HAVE_THE_SAME_SUPERTYPES_AS_NON_FINAL_EXPECT_CLASSIFIER_WARNING")
internal actual abstract class CompletionHandlerBase actual constructor() : LockFreeLinkedListNode(), CompletionHandler {
    actual abstract override fun invoke(cause: Throwable?)
}

internal actual inline val CompletionHandlerBase.asHandler: CompletionHandler get() = this

// fixme replace the suppress with AllowDifferentMembersInActual once stdlib is updated to 1.9.20 https://github.com/Kotlin/kotlinx.coroutines/issues/3846
// New 'CompletionHandler` supertype is added compared to the expect declaration.
// Probably we can add it to JS and common too, to avoid the suppression/opt-in
@Suppress("ACTUAL_CLASSIFIER_MUST_HAVE_THE_SAME_SUPERTYPES_AS_NON_FINAL_EXPECT_CLASSIFIER_WARNING")
internal actual abstract class CancelHandlerBase actual constructor() : CompletionHandler {
    actual abstract override fun invoke(cause: Throwable?)
}

internal actual inline val CancelHandlerBase.asHandler: CompletionHandler get() = this

@Suppress("NOTHING_TO_INLINE")
internal actual inline fun CompletionHandler.invokeIt(cause: Throwable?) = invoke(cause)
