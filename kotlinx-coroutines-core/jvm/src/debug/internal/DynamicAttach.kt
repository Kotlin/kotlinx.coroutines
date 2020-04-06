/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */
package kotlinx.coroutines.debug.internal

private val noop = {}
/*
 * Use dynamic attach if kotlinx-coroutines-debug is present in the classpath
 */
internal val attach = getFunction("kotlinx.coroutines.debug.internal.ByteBuddyDynamicAttach") ?: noop
internal val detach = getFunction("kotlinx.coroutines.debug.internal.ByteBuddyDynamicDetach") ?: noop

@Suppress("UNCHECKED_CAST")
private fun getFunction(clzName: String): Function0<Unit>? = runCatching {
    val clz = Class.forName(clzName)
    val ctor = clz.constructors[0]
    ctor.newInstance() as Function0<Unit>
}.getOrNull()

