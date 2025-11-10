import org.jetbrains.kotlin.gradle.ExperimentalWasmDsl

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

val allMetadataJar by tasks.getting(Jar::class) {
    manifest {
        attributes("Automatic-Module-Name" to "kotlinx.coroutines.test.artifact_disambiguating_module")
    }
}
