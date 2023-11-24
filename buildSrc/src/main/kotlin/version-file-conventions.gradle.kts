import org.gradle.api.tasks.bundling.*

/* `kotlinx-coroutines-debug` configures `VersionFile` on its own when the corresponding task is created. */
val invalidModules = listOf("kotlinx-coroutines-debug")

configure(subprojects.filter {
    !unpublished.contains(it.name) && !invalidModules.contains(it.name) && it.name !in sourceless
}) {
    val project = this
    val jarTaskName = if (isMultiplatform) "jvmJar" else "jar"
    val versionFileTask = VersionFile.registerVersionFileTask(project)
    tasks.withType(Jar::class.java).configureEach {
        if (name == jarTaskName) {
            VersionFile.fromVersionFile(this, versionFileTask)
        }
    }
}
