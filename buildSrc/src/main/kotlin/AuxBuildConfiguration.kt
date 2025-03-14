import CacheRedirector.configure
import org.gradle.api.Project
import org.gradle.api.tasks.*
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
            workaroundForCleanTask()
            CacheRedirector.configure(this)
            workaroundForCoroutinesLeakageToClassPath()
        }

        CacheRedirector.configureJsPackageManagers(rootProject)

        // Sigh, there is no BuildScanExtension in classpath when there is no --scan
        rootProject.extensions.findByName("buildScan")?.withGroovyBuilder {
            setProperty("termsOfServiceUrl", "https://gradle.com/terms-of-service")
            setProperty("termsOfServiceAgree", "yes")
        }
    }

    private fun Project.workaroundForCleanTask() {
        // the 'clean' task cannot delete expanded.lock file on Windows as it is still held by Gradle, failing the build
        // Gradle issue: https://github.com/gradle/gradle/issues/25752
        tasks {
            val clean by existing(Delete::class) {
                setDelete(fileTree(layout.buildDirectory) {
                    exclude("tmp/.cache/expanded/expanded.lock")
                })
            }
        }
    }

    /*
     * 'kotlinx-coroutines-core' dependency leaks into test runtime classpath via 'kotlin-compiler-embeddable'
     * and conflicts with our own test/runtime incompatibilities (e.g. when class is moved from a main to test),
     * so we do substitution here.
     * TODO figure out if it's still the problem
     */
    private fun Project.workaroundForCoroutinesLeakageToClassPath() {
        configurations
            .matching {
                // Excluding substituted project itself because of circular dependencies, but still do it
                // for "*Test*" configurations
                name != coreModule || it.name.contains("Test")
            }
            .configureEach {
                resolutionStrategy.dependencySubstitution {
                    substitute(module("org.jetbrains.kotlinx:$coreModule"))
                        .using(project(":$coreModule"))
                        .because(
                            "Because Kotlin compiler embeddable leaks coroutines into the runtime classpath, " +
                                "triggering all sort of incompatible class changes errors"
                        )
                }
            }
    }
}
