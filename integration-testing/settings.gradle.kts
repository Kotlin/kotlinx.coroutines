pluginManagement {
    repositories {
        mavenCentral()
        maven("https://plugins.gradle.org/m2/")
        maven("https://maven.pkg.jetbrains.space/kotlin/p/kotlin/dev")
        maven("https://redirector.kotlinlang.org/maven/dev")
        maven("file:///Users/Nikolay.Lunyak/Documents/Projects/kotlin-worktrees/kotlin-platform-type-commonized-to-different-types/build/repo")
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
