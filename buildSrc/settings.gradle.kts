pluginManagement {
    val buildSnapshotTrain = providers.gradleProperty("build_snapshot_train").orNull
    repositories {
        maven("https://cache-redirector.jetbrains.com/plugins.gradle.org/m2")
        if (buildSnapshotTrain?.toBoolean() == true) {
            mavenLocal()
        }

        maven("https://cache-redirector.jetbrains.com/repo.maven.apache.org/maven2")
    }
}
