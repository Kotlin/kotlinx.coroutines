pluginManagement {
    val build_snapshot_train: String? by settings
    repositories {
        val cacheRedirectorEnabled = System.getenv("CACHE_REDIRECTOR")?.toBoolean() == true
        if (cacheRedirectorEnabled) {
            println("Redirecting repositories for buildSrc buildscript")
            maven("https://cache-redirector.jetbrains.com/plugins.gradle.org/m2")
        } else {
            maven("https://plugins.gradle.org/m2")
        }
        if (build_snapshot_train?.toBoolean() == true) {
            mavenLocal()
        }
    }
}
