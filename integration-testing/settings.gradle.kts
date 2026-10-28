apply(from = "../buildSrc/src/main/kotlin/repositories.settings.gradle.kts")

dependencyResolutionManagement {
    repositories {
        maven(rootProject.projectDir.toURI().resolve("../build/build-local-repository/"))
    }
}

include("smokeTest")
include("safeDebugAgentTest")
include("java8Test")
include(":jpmsTest")
include("r8Test")

rootProject.name = "kotlinx-coroutines-integration-testing"
