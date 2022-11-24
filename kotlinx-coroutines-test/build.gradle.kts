/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

import org.jetbrains.kotlin.gradle.plugin.mpp.*

val experimentalAnnotations = listOf(
    "kotlin.Experimental",
    "kotlinx.coroutines.ExperimentalCoroutinesApi",
    "kotlinx.coroutines.InternalCoroutinesApi"
)

kotlin {
    sourceSets.all { configureMultiplatform() }

    targets.withType(KotlinNativeTargetWithTests::class.java).configureEach {
        binaries.getTest("DEBUG").apply {
            optimized = true
            binaryOptions["memoryModel"] = "experimental"
        }
    }

    sourceSets {
        jvmTest {
            dependencies {
                implementation(project(":kotlinx-coroutines-debug"))
            }
        }
    }

    wasm {
        d8 {
            testTask {
                filter.apply {
                    excludeTest("RunTestTest", "testRunTestWithSmallTimeout")
                    excludeTest("RunTestTest", "testRunTestWithLargeTimeout")
                    excludeTest("RunTestTest", "testRunTestTimingOutAndThrowing")
                    excludeTest("RunTestTest", "testCoroutineCompletingWithoutDispatch")
                    excludeTest("TestDispatchersTest", "testMainMocking")
                    excludeTest("TestDispatchersTest", "testMockedMainImplementsDelay")
                }
            }
        }
    }
}
