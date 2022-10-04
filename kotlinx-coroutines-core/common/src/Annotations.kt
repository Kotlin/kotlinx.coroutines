/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

import kotlinx.coroutines.flow.*

/**
 * Marks declarations in the coroutines that are **delicate** &mdash;
 * they have limited use-case and shall be used with care in general code.
 * Any use of a delicate declaration has to be carefully reviewed to make sure it is
 * properly used and does not create problems like memory and resource leaks.
 * Carefully read documentation of any declaration marked as `DelicateCoroutinesApi`.
 */
@MustBeDocumented
@Retention(value = AnnotationRetention.BINARY)
@RequiresOptIn(
    level = RequiresOptIn.Level.WARNING,
    message = "This is a delicate API and its use requires care." +
        " Make sure you fully read and understand documentation of the declaration that is marked as a delicate API."
)
public annotation class DelicateCoroutinesApi

/**
 * Marks declarations that are still **experimental** in coroutines API, which means that the design of the
 * corresponding declarations has open issues which may (or may not) lead to their changes in the future.
 * Roughly speaking, there is a chance that those declarations will be deprecated in the near future or
 * the semantics of their behavior may change in some way that may break some code.
 */
@MustBeDocumented
@Retention(value = AnnotationRetention.BINARY)
@Target(
    AnnotationTarget.CLASS,
    AnnotationTarget.ANNOTATION_CLASS,
    AnnotationTarget.PROPERTY,
    AnnotationTarget.FIELD,
    AnnotationTarget.LOCAL_VARIABLE,
    AnnotationTarget.VALUE_PARAMETER,
    AnnotationTarget.CONSTRUCTOR,
    AnnotationTarget.FUNCTION,
    AnnotationTarget.PROPERTY_GETTER,
    AnnotationTarget.PROPERTY_SETTER,
    AnnotationTarget.TYPEALIAS
)
@RequiresOptIn(level = RequiresOptIn.Level.WARNING)
public annotation class ExperimentalCoroutinesApi

/**
 * Marks [Flow]-related API as a feature preview.
 *
 * Flow preview has **no** backward compatibility guarantees, including both binary and source compatibility.
 * Its API and semantics can and will be changed in next releases.
 *
 * Feature preview can be used to evaluate its real-world strengths and weaknesses, gather and provide feedback.
 * According to the feedback, [Flow] will be refined on its road to stabilization and promotion to a stable API.
 *
 * The best way to speed up preview feature promotion is providing the feedback on the feature.
 */
@MustBeDocumented
@Retention(value = AnnotationRetention.BINARY)
@RequiresOptIn(
    level = RequiresOptIn.Level.WARNING,
    message = "This declaration is in a preview state and can be changed in a backwards-incompatible manner with a best-effort migration. " +
            "Its usage should be marked with '@kotlinx.coroutines.FlowPreview' or '@OptIn(kotlinx.coroutines.FlowPreview::class)' " +
            "if you accept the drawback of relying on preview API"
)
@Target(AnnotationTarget.CLASS, AnnotationTarget.FUNCTION, AnnotationTarget.TYPEALIAS, AnnotationTarget.PROPERTY)
public annotation class FlowPreview

/**
 * Marks declarations that are **obsolete** in coroutines API, which means that the design of the corresponding
 * declarations has serious known flaws and they will be redesigned in the future.
 * Roughly speaking, these declarations will be deprecated in the future but there is no replacement for them yet,
 * so they cannot be deprecated right away.
 */
@MustBeDocumented
@Retention(value = AnnotationRetention.BINARY)
@RequiresOptIn(level = RequiresOptIn.Level.WARNING)
public annotation class ObsoleteCoroutinesApi

/**
 * Marks declarations that are **internal** in coroutines API, which means that should not be used outside of
 * `kotlinx.coroutines`, because their signatures and semantics will change between future releases without any
 * warnings and without providing any migration aids.
 */
@Retention(value = AnnotationRetention.BINARY)
@Target(AnnotationTarget.CLASS, AnnotationTarget.FUNCTION, AnnotationTarget.TYPEALIAS, AnnotationTarget.PROPERTY)
@RequiresOptIn(
    level = RequiresOptIn.Level.ERROR, message = "This is an internal kotlinx.coroutines API that " +
            "should not be used from outside of kotlinx.coroutines. No compatibility guarantees are provided. " +
            "It is recommended to report your use-case of internal API to kotlinx.coroutines issue tracker, " +
            "so stable API could be provided instead"
)
public annotation class InternalCoroutinesApi
