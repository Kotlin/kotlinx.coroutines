/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package cases.localClasses


class L {
    internal fun a(lambda: () -> Unit) = lambda()

    @Suppress("NOTHING_TO_INLINE")
    internal inline fun inlineLambda() {
        a {
            println("OK")
        }
    }
}

fun box() {
    L().inlineLambda()
}


// TODO: inline lambda from stdlib