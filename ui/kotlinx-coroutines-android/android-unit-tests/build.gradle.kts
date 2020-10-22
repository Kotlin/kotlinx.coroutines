/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

dependencies {
    jvmTestImplementation("com.google.android:android:${version("android")}")
    jvmTestImplementation("org.robolectric:robolectric:${version("robolectric")}")
    jvmTestImplementation(project(":kotlinx-coroutines-test"))
    jvmTestImplementation(project(":kotlinx-coroutines-android"))
}
