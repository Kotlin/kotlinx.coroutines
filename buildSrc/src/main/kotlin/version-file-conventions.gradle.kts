import org.gradle.api.tasks.bundling.*

configure(subprojects.filter { !unpublished.contains(it.name) && it.name !in sourceless }) {
    val project = this
    val jarTaskName = when {
        project.name == "kotlinx-coroutines-debug" -> {
            project.apply(plugin = "com.github.johnrengelman.shadow")
            "shadowJar"
        }
        isMultiplatform -> "jvmJar"
        else -> "jar"
    }
    val versionFileTask = VersionFile.registerVersionFileTask(project)
    tasks.withType(Jar::class.java).named(jarTaskName) {
        VersionFile.fromVersionFile(this, versionFileTask)
    }
}
