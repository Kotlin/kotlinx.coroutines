/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

/**
 * Marks declarations that are still **experimental** in coroutines API, which means that the design of the
 * corresponding declarations has open issues which may (or may not) lead to their changes in the future.
 * Roughly speaking, there is a chance that those declarations will be deprecated in the near future or
 * the semantics of their behavior may change in some way that may break some code.
 */
@MustBeDocumented
@Retention(value = AnnotationRetention.BINARY)
@Experimental(level = Experimental.Level.WARNING)
public annotation class ExperimentalCoroutinesApi

/**
 * Marks declarations that are **obsolete** in coroutines API, which means that the design of the corresponding
 * declarations has serious known flaws and they will be redesigned in the future.
 * Roughly speaking, these declarations will be deprecated in the future but there is no replacement for them yet,
 * so they cannot be deprecated right away.
 */
@MustBeDocumented
@Retention(value = AnnotationRetention.BINARY)
@Experimental(level = Experimental.Level.WARNING)
public annotation class ObsoleteCoroutinesApi

/**
 * Marks declarations that are **internal** in coroutines API, which means that should not be used outside of
 * `kotlinx.coroutines`, because their signatures and semantics will be changing between release without any
 * warnings and without providing any migration aids.
 *
 * @suppress **This an internal API and should not be used from general code.**
 */
@Retention(value = AnnotationRetention.BINARY)
@Experimental(level = Experimental.Level.ERROR)
public annotation class InternalCoroutinesApi
