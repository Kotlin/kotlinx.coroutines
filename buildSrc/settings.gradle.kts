pluginManagement {
    val buildSnapshotTrain = providers.gradleProperty("build_snapshot_train").orNull
    repositories {
        val cacheRedirectorEnabled = System.getenv("CACHE_REDIRECTOR")?.toBoolean() == true
        if (cacheRedirectorEnabled) {
            println("Redirecting repositories for buildSrc buildscript")
            maven("https://cache-redirector.jetbrains.com/plugins.gradle.org/m2")
        } else {
            maven("https://plugins.gradle.org/m2")
        }
        if (buildSnapshotTrain?.toBoolean() == true) {
            mavenLocal()
        }
    }
}
