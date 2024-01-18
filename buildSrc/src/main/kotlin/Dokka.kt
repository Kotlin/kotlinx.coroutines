import org.gradle.api.*
import org.gradle.kotlin.dsl.*
import org.jetbrains.dokka.gradle.*
import java.io.*
import java.net.*

/**
 * Package-list by external URL for documentation generation.
 */
fun Project.externalDocumentationLink(
    url: String,
    packageList: File = projectDir.resolve("package.list")
) {
    tasks.withType<AbstractDokkaLeafTask>().configureEach {
        dokkaSourceSets.configureEach {
            externalDocumentationLink {
                this.url = URL(url)
                packageListUrl = packageList.toPath().toUri().toURL()
            }
        }
    }
}
