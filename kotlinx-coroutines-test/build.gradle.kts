import org.jetbrains.kotlin.gradle.plugin.mpp.*

/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

val experimentalAnnotations = listOf(
    "kotlin.Experimental",
    "kotlinx.coroutines.ExperimentalCoroutinesApi",
    "kotlinx.coroutines.InternalCoroutinesApi"
)

kotlin {
    sourceSets.all { configureMultiplatform() }

    targets.withType(KotlinNativeTargetWithTests::class.java).configureEach {
        val tests = binaries.getTest("DEBUG")
        tests.optimized = true
        tests.binaryOptions["memoryModel"] = "experimental"
    }
}
