/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

project.configureAar()

dependencies {
    configureAarUnpacking()

    testImplementation("com.google.android:android:${version("android")}")
    testImplementation("org.robolectric:robolectric:${version("robolectric")}")
    // Required by robolectric
    testImplementation("androidx.test:core:1.2.0")
    testImplementation("androidx.test:monitor:1.2.0")

    testImplementation(project(":kotlinx-coroutines-test"))
    testImplementation(project(":kotlinx-coroutines-android"))
}
