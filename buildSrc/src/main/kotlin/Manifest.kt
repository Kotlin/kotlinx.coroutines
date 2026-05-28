import org.gradle.api.Project
import org.gradle.api.tasks.bundling.Jar
import org.gradle.kotlin.dsl.attributes

/**
 * Fills `Implementation-Title`, `Implementation-Version` and `Implementation-Vendor`
 * attributes using information from the given [project].
 *
 * Note that `Implementation-Vendor` is always `JetBrains`.
 */
fun Jar.fillManifestImplementationAttributes(project: Project) {
    manifest {
        attributes(
            "Implementation-Title" to project.name,
            "Implementation-Version" to project.version.toString(),
            "Implementation-Vendor" to "JetBrains",
        )
    }
}
