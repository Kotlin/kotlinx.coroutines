kotlin {
    sourceSets {
        jvmTest {
            dependencies {
                implementation(project(":kotlinx-coroutines-debug"))
            }
        }
    }
}
