@file:Suppress("UnstableApiUsage")

import groovy.util.Node
import groovy.util.NodeList
import groovy.xml.XmlParser
import org.gradle.api.Project
import org.gradle.api.publish.PublishingExtension
import org.gradle.api.publish.maven.*
import org.gradle.api.publish.maven.tasks.AbstractPublishToMaven
import org.gradle.api.publish.maven.tasks.GenerateMavenPom
import org.gradle.api.tasks.*
import org.gradle.api.tasks.bundling.Jar
import org.gradle.kotlin.dsl.*
import org.gradle.plugins.signing.*

// Pom configuration

fun MavenPom.configureMavenCentralMetadata(project: Project) {
    name = project.name
    description = "Coroutines support libraries for Kotlin"
    url = "https://github.com/Kotlin/kotlinx.coroutines"

    licenses {
        license {
            name = "Apache-2.0"
            url = "https://www.apache.org/licenses/LICENSE-2.0.txt"
            distribution = "repo"
        }
    }

    developers {
        developer {
            id = "JetBrains"
            name = "JetBrains Team"
            organization = "JetBrains"
            organizationUrl = "https://www.jetbrains.com"
        }
    }

    scm {
        url = "https://github.com/Kotlin/kotlinx.coroutines"
    }
}

fun signPublicationIfKeyPresent(project: Project, publication: MavenPublication) {
    val keyId = project.getSensitiveProperty("libs.sign.key.id")
    val signingKey = project.getSensitiveProperty("libs.sign.key.private")
    val signingKeyPassphrase = project.getSensitiveProperty("libs.sign.passphrase")
    if (!signingKey.isNullOrBlank()) {
        project.extensions.configure<SigningExtension>("signing") {
            useInMemoryPgpKeys(keyId, signingKey, signingKeyPassphrase)
            sign(publication)
        }
    }
}

private fun Project.getSensitiveProperty(name: String): String? {
    return project.providers.gradleProperty(name).orNull ?: project.providers.environmentVariable(name).orNull
}

/**
 * This unbelievable piece of engineering^W programming is a workaround for the following issues:
 * - https://github.com/gradle/gradle/issues/26132
 * - https://youtrack.jetbrains.com/issue/KT-61313/
 *
 * Long story short:
 * 1) Single module produces multiple publications
 * 2) 'Sign' plugin signs them
 * 3) Signature files are re-used, which Gradle detects and whines about an implicit dependency
 *
 * There are three patterns that we workaround:
 * 1) 'Sign' does not depend on 'publish'
 * 2) Empty 'javadoc.jar.asc' got reused between publications (kind of a implication of the previous one)
 * 3) `klib` signatures are reused where appropriate
 *
 * It addresses the following failures:
 * ```
 * Gradle detected a problem with the following location: 'kotlinx.coroutines/kotlinx-coroutines-core/build/classes/kotlin/macosArm64/main/klib/kotlinx-coroutines-core.klib.asc'.
 * Reason: Task ':kotlinx-coroutines-core:linkWorkerTestDebugTestMacosArm64' uses this output of task ':kotlinx-coroutines-core:signMacosArm64Publication' without declaring an explicit or implicit dependency. This can lead to incorrect results being produced, depending on what order the tasks are executed.
 *
 * ```
 * and
 * ```
 * Gradle detected a problem with the following location: 'kotlinx-coroutines-core/build/libs/kotlinx-coroutines-core-1.7.2-SNAPSHOT-javadoc.jar.asc'.
 * Reason: Task ':kotlinx-coroutines-core:publishAndroidNativeArm32PublicationToMavenLocal' uses this output of task ':kotlinx-coroutines-core:signAndroidNativeArm64Publication' without declaring an explicit or implicit dependency.
 * ```
 */
fun Project.establishSignDependencies() {
    tasks.withType<Sign>().configureEach {
        val pubName = name.removePrefix("sign").removeSuffix("Publication")
        // Gradle#26132 -- establish dependency between sign and link tasks, as well as compile ones
        mustRunAfter(tasks.matching { it.name == "linkDebugTest$pubName" })
        mustRunAfter(tasks.matching { it.name == "linkWorkerTestDebugTest$pubName" })
        mustRunAfter(tasks.matching { it.name == "compileTestKotlin$pubName" })
    }

    // Sign plugin issues and publication:
    // Establish dependency between 'sign' and 'publish*' tasks
    tasks.withType<AbstractPublishToMaven>().configureEach {
        dependsOn(tasks.withType<Sign>())
    }
}

/**
 * Re-configure common publication to depend on JVM artifact only in pom.xml.
 * It allows us to keep backwards compatibility with pre-multiplatform 'kotlinx-coroutines' publication scheme
 * for Maven consumers:
 * - Previously, we published 'kotlinx-coroutines-core' as the JVM artifact
 * - With a multiplatform enabled as is, 'kotlinx-coroutines-core' is a common artifact not consumable from Maven,
 *   instead, users should depend on 'kotlinx-coroutines-core-jvm'
 * - To keep the compatibility and experience, we do add dependency on 'kotlinx-coroutines-core-jvm' for
 *   'kotlinx-coroutines-core' in pom.xml only (e.g. Gradle will keep using the metadata), so Maven users can
 *   depend on previous coordinates.
 *
 * Original code comment:
 *  Publish the platform JAR and POM so that consumers who depend on this module and can't read Gradle module
 *  metadata can still get the platform artifact and transitive dependencies from the POM.
 */
public fun Project.reconfigureMultiplatformPublication(jvmPublication: MavenPublication) {
    val mavenPublications =
        extensions.getByType(PublishingExtension::class.java).publications.withType<MavenPublication>()

    // 1: find KMP publication
    val kmpPublication = mavenPublications.getByName("kotlinMultiplatform")

    val jvmPomTaskName = "generatePomFileFor${jvmPublication.name.replaceFirstChar(Char::uppercaseChar)}Publication"
    tasks.withType(GenerateMavenPom::class.java)
        .matching { it.name == "generatePomFileForKotlinMultiplatformPublication" }
        .configureEach {
            // 2: find pure JVM publication and capture path to where pom.xml will be stored.
            // This is the only part of the serialized task state we have here, we don't have a publication, an XML,
            // and we for sure cannot rebuild it on a cache-hit path
            val jvmPomTask = tasks.named(jvmPomTaskName, GenerateMavenPom::class.java)
            // Execution dependency
            dependsOn(jvmPomTask)
            // .get() gets a _configured_ task, so this is safe
            // (both tasks are configured at the same time, and .get() is kind of an event loop for conf)
            val jvmPomFile = jvmPomTask.get().destination
            val kmpArtifactId = kmpPublication.artifactId

            // 3: take KMP publication and do the trick:
            // 3.1: remove all the content from KMP pom.xml
            // 3.2 take JVM pom.xml and copy it into KMP pom.xml
            // 3.3 patch "KMP" pom.xml to have root artifactId (without -jvm) back
            // 3.4 patch "KMP" pom.xml so it's pure packaging (only POM, no artifacts)
            // 3.5 patch "KMP" pom.xml to depend only on the JVM publication
            pom.withXml {
                // This closure is a serialized task state. The only thing it can capture from another
                // configured publication (note: it's not executed!) is path where we can expect an XML on the execution phase
                val jvmPom = XmlParser(false, false).parse(jvmPomFile)
                val jvmGroupId = ((jvmPom["groupId"] as NodeList).first() as Node).text()
                val jvmArtifactId = ((jvmPom["artifactId"] as NodeList).first() as Node).text()
                val jvmVersion = ((jvmPom["version"] as NodeList).first() as Node).text()

                val root = asNode()
                // Remove the original content and add the content from the platform POM:
                root.children().toList().forEach { root.remove(it as Node) }
                jvmPom.children().toList().forEach { root.append(it as Node) }

                // Adjust the self artifact ID, as it should match the root module's coordinates:
                ((root["artifactId"] as NodeList).first() as Node).setValue(kmpArtifactId)

                // Set packaging to POM to indicate that there's no artifact:
                root.appendNode("packaging", "pom")

                // Remove the original platform dependencies and add a single dependency on the platform module:
                val dependencies = (root["dependencies"] as NodeList).first() as Node
                dependencies.children().toList().forEach { dependencies.remove(it as Node) }
                dependencies.appendNode("dependency").apply {
                    appendNode("groupId", jvmGroupId)
                    appendNode("artifactId", jvmArtifactId)
                    appendNode("version", jvmVersion)
                    appendNode("scope", "compile")
                }
            }
        }
}

// Top-level deploy task that publishes all artifacts
public fun Project.registerTopLevelDeployTask() {
    assert(this === rootProject)
    tasks.register("deploy") {
        allprojects {
            val publishTasks = tasks.matching { it.name == "publish" }
            dependsOn(publishTasks)
        }
    }
}

public fun Project.registerEmptyJavadocArtifact(): TaskProvider<Jar> {
    return tasks.register("javadocJar", Jar::class) {
        archiveClassifier = "javadoc"
        // contents are deliberately left empty
    }
}

