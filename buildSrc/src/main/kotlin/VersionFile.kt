import org.gradle.api.*
import org.gradle.api.tasks.*

/**
 * Adds 'module_name.version' file to the project's JAR META-INF
 * for the better toolability. See #2941
 */
object VersionFile {
    fun registerVersionFileTask(project: Project): TaskProvider<Task> {
        val versionFile = project.layout.buildDirectory.file("${project.name.replace('-', '_')}.version")
        val version = project.version.toString()
        return project.tasks.register("versionFileTask") {
            outputs.file(versionFile)
            doLast {
                versionFile.get().asFile.writeText(version)
            }
        }
    }

    fun fromVersionFile(target: AbstractCopyTask, versionFileTask: TaskProvider<Task>) {
        target.from(versionFileTask) {
            into("META-INF")
        }
    }
}
