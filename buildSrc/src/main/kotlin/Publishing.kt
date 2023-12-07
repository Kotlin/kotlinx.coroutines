/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

@file:Suppress("UnstableApiUsage")

import groovy.util.Node
import groovy.util.NodeList
import org.gradle.api.Project
import org.gradle.api.XmlProvider
import org.gradle.api.artifacts.dsl.*
import org.gradle.api.publish.PublishingExtension
import org.gradle.api.publish.maven.*
import org.gradle.api.publish.maven.tasks.AbstractPublishToMaven
import org.gradle.api.tasks.*
import org.gradle.api.tasks.bundling.Jar
import org.gradle.kotlin.dsl.*
import org.gradle.plugins.signing.*
import java.net.*

// Pom configuration

fun MavenPom.configureMavenCentralMetadata(project: Project) {
    name by project.name
    description by "Coroutines support libraries for Kotlin"
    url by "https://github.com/Kotlin/kotlinx.coroutines"

    licenses {
        license {
            name by "The Apache Software License, Version 2.0"
            url by "https://www.apache.org/licenses/LICENSE-2.0.txt"
            distribution by "repo"
        }
    }

    developers {
        developer {
            id by "JetBrains"
            name by "JetBrains Team"
            organization by "JetBrains"
            organizationUrl by "https://www.jetbrains.com"
        }
    }

    scm {
        url by "https://github.com/Kotlin/kotlinx.coroutines"
    }
}

fun mavenRepositoryUri(): URI {
    val repositoryId: String? = System.getenv("libs.repository.id")
    return if (repositoryId == null) {
        URI("https://oss.sonatype.org/service/local/staging/deploy/maven2/")
    } else {
        URI("https://oss.sonatype.org/service/local/staging/deployByRepositoryId/$repositoryId")
    }
}

fun configureMavenPublication(rh: RepositoryHandler, project: Project) {
    rh.maven {
        url = mavenRepositoryUri()
        credentials {
            username = project.getSensitiveProperty("libs.sonatype.user")
            password = project.getSensitiveProperty("libs.sonatype.password")
        }
    }

    // Something that's easy to "clean" for development, not mavenLocal
    rh.maven("${project.rootProject.buildDir}/repo") {
        name = "buildRepo"
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
    return project.findProperty(name) as? String ?: System.getenv(name)
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
    val kmpPublication = mavenPublications.getByName("kotlinMultiplatform")

    // TODO: this one can be rewritten in a more straightforward manner
    // right now it's translated almost as-is from Groovy
    var platformXml: XmlProvider? = null
    jvmPublication.pom.withXml { platformXml = this }

    kmpPublication.pom.withXml {
        val root = asNode()
        // Remove the original content and add the content from the platform POM:
        root.children().toList().forEach { root.remove(it as Node) }
        platformXml!!.asNode().children().forEach { root.append(it as Node) }

        // Adjust the self artifact ID, as it should match the root module's coordinates:
        ((root.get("artifactId") as NodeList).get(0) as Node).setValue(kmpPublication.artifactId)

        // Set packaging to POM to indicate that there's no artifact:
        root.appendNode("packaging", "pom")

        // Remove the original platform dependencies and add a single dependency on the platform module:
        val dependencies = (root.get("dependencies") as NodeList).get(0) as Node
        dependencies.children().toList().forEach { dependencies.remove(it as Node) }
        val singleDependency = dependencies.appendNode("dependency")
        singleDependency.appendNode("groupId", jvmPublication.groupId)
        singleDependency.appendNode("artifactId", jvmPublication.artifactId)
        singleDependency.appendNode("version", jvmPublication.version)
        singleDependency.appendNode("scope", "compile")
    }

    // TODO verify if this is still relevant
    tasks.matching { it.name == "generatePomFileForKotlinMultiplatformPublication" }.configureEach {
        @Suppress("DEPRECATION")
        dependsOn(tasks["generatePomFileFor${jvmPublication.name.capitalize()}Publication"])
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
        archiveClassifier.set("javadoc")
        // contents are deliberately left empty
    }
}

