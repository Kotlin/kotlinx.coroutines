import org.gradle.api.*
import org.gradle.api.publish.PublishingExtension
import org.gradle.kotlin.dsl.*
import org.jetbrains.dokka.gradle.DokkaExtension
import java.io.*
import java.net.*

/**
 * Package-list by external URL for documentation generation.
 */
fun Project.configureExternalLinks(
    url: String,
    packageList: File = projectDir.resolve("package.list")
) {
    extensions.configure<DokkaExtension> {
        dokkaSourceSets.configureEach {
            externalDocumentationLinks.register("api") {
                this.url = URI.create(url)
                this.packageListUrl = packageList.toURI()
            }
        }
    }
}
