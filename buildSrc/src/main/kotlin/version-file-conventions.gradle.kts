import org.gradle.api.tasks.bundling.*

configure(subprojects.filter { !unpublished.contains(it.name) && it.name !in sourceless }) {
    val project = this
    val jarTaskName = when {
        isMultiplatform -> "jvmJar"
        else -> "jar"
    }
    val versionFileTask = VersionFile.registerVersionFileTask(project)
    tasks.withType(Jar::class.java).named(jarTaskName) {
        VersionFile.fromVersionFile(this, versionFileTask)
    }
}
