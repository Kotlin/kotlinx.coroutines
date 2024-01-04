/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.internal

internal expect class ReentrantLock() {
    fun tryLock(): Boolean
    fun unlock()
}

internal expect inline fun <T> ReentrantLock.withLock(action: () -> T): T

internal expect fun <E> identitySet(expectedSize: Int): MutableSet<E>

/**
 * Annotation indicating that the marked property is the subject of benign data race.
 * LLVM does not support this notion, so on K/N platforms we alias it into `@Volatile` to prevent potential OoTA.
 *
 * The purpose of this annotation is not to save an extra-volatile on JVM platform, but rather to explicitly emphasize
 * that data-race is benign.
 */
@OptionalExpectation
@Target(AnnotationTarget.FIELD)
internal expect annotation class BenignDataRace()
