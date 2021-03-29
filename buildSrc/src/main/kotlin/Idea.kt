/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

object Idea {
    @JvmStatic // for Gradle
    val active: Boolean
        get() = System.getProperty("idea.active") == "true"
}
