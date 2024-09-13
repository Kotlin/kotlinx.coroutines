import org.jetbrains.kotlin.gradle.plugin.mpp.*
import org.jetbrains.kotlin.gradle.targets.js.dsl.*

kotlin {
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
