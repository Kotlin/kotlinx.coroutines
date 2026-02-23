pluginManagement {
    repositories {
        mavenCentral()
        maven("https://plugins.gradle.org/m2/")
        maven("https://maven.pkg.jetbrains.space/kotlin/p/kotlin/dev")
        maven("https://redirector.kotlinlang.org/maven/dev")
        val kotlinRepoUrl = providers.gradleProperty("kotlin_repo_url").orNull
        if (!kotlinRepoUrl.isNullOrBlank()) {
            maven(kotlinRepoUrl)
        }
        mavenLocal()
    }
}

include("smokeTest")
include("safeDebugAgentTest")
include("java8Test")
include(":jpmsTest")

rootProject.name = "kotlinx-coroutines-integration-testing"
