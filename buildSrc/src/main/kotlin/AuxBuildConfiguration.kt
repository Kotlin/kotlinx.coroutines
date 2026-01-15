import org.gradle.api.*
import org.gradle.kotlin.dsl.*

/**
 * Auxiliary build configuration that is grouped in a single place for convenience:
 * - Workarounds for Gradle/KGP issues
 * - Cache redirector
 */
object AuxBuildConfiguration {

    @JvmStatic
    fun configure(rootProject: Project) {
        rootProject.allprojects {
            CacheRedirector.configure(this)
        }

        CacheRedirector.configureRootJsPackageManagers(rootProject)

        // Sigh, there is no BuildScanExtension in classpath when there is no --scan
        rootProject.extensions.findByName("buildScan")?.withGroovyBuilder {
            setProperty("termsOfServiceUrl", "https://gradle.com/terms-of-service")
            setProperty("termsOfServiceAgree", "yes")
        }
    }
}
