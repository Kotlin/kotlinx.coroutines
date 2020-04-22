/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

dependencies {
    testImplementation("com.google.android:android:${property("android_version")}")
    testImplementation("org.robolectric:robolectric:${property("robolectric_version")}")
    testImplementation(project(":kotlinx-coroutines-test"))
    testImplementation(project(":kotlinx-coroutines-android"))
}
