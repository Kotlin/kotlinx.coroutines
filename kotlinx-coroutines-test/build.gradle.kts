import org.jetbrains.kotlin.gradle.ExperimentalWasmDsl
import org.jetbrains.kotlin.gradle.plugin.mpp.*

kotlin {
    targets.withType(KotlinNativeTargetWithTests::class.java).configureEach {
        binaries.getTest("DEBUG").apply {
            optimized = true
        }
    }

    sourceSets {
        jvmTest {
            dependencies {
                implementation(project(":kotlinx-coroutines-debug"))
            }
        }
    }

    @OptIn(ExperimentalWasmDsl::class)
    wasmJs {
        nodejs {
            testTask {
                filter.apply {
                    // https://youtrack.jetbrains.com/issue/KT-61888
                    excludeTest("TestDispatchersTest", "testMainMocking")
                }
            }
        }
    }
}
