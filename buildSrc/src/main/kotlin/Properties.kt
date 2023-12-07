/*
 * Copyright 2016-2023 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

import org.gradle.api.*
import org.gradle.api.provider.*

infix fun <T> Property<T>.by(value: T) {
    set(value)
}

val Project.jdkToolchainVersion: Int get() = property("jdk_toolchain_version").toString().toInt()

val Project.nativeTargetsAreEnabled: Boolean get() = rootProject.properties["disable_native_targets"] == null
