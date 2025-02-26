pluginManagement {
    repositories {
        mavenCentral()
        maven("https://plugins.gradle.org/m2/")
        maven("https://maven.pkg.jetbrains.space/kotlin/p/kotlin/dev")
        maven("https://redirector.kotlinlang.org/maven/dev")
        mavenLocal()
    }
}

include("smokeTest")
include("java8Test")
include(":jpmsTest")

rootProject.name = "kotlinx-coroutines-integration-testing"
