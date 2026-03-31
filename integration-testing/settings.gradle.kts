pluginManagement {
    repositories {
        mavenCentral()
        maven("https://plugins.gradle.org/m2/")
        maven("https://maven.pkg.jetbrains.space/kotlin/p/kotlin/dev")
        mavenLocal()
        val kotlinRepoUrl = providers.gradleProperty("kotlin_repo_url").orNull
        if (!kotlinRepoUrl.isNullOrBlank()) {
            maven(kotlinRepoUrl)
        }
    }
}

include("smokeTest")
include("safeDebugAgentTest")
include("java8Test")
include(":jpmsTest")
include("r8Test")

rootProject.name = "kotlinx-coroutines-integration-testing"
