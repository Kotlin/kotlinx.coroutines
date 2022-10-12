/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

import ru.vyarus.gradle.plugin.animalsniffer.*

configure(subprojects) {
    // Skip JDK 8 projects or unpublished ones
    if (!shouldSniff()) return@configure
    apply(plugin = "ru.vyarus.animalsniffer")
    project.plugins.withType(JavaPlugin::class.java) {
        configure<AnimalSnifferExtension> {
            sourceSets = listOf((project.extensions.getByName("sourceSets") as SourceSetContainer).getByName("main"))
        }
        val signature: Configuration by configurations
        dependencies {
            signature("net.sf.androidscents.signature:android-api-level-14:4.0_r4@signature")
            signature("org.codehaus.mojo.signature:java17:1.0@signature")
        }

        if (project.name == coreModule) {
            // Specific files so nothing from core is accidentally skipped
            tasks.withType<AnimalSniffer>().configureEach {
                exclude("**/future/FutureKt*")
                exclude("**/future/ContinuationHandler*")
                exclude("**/future/CompletableFutureCoroutine*")

                exclude("**/stream/StreamKt*")
                exclude("**/stream/StreamFlow*")

                exclude("**/time/TimeKt*")
            }
        }
    }
}

fun Project.shouldSniff(): Boolean {
    // Skip all non-JVM projects
    if (platformOf(project) != "jvm") return false
    val name = project.name
    if (name in unpublished || name in sourceless || name in androidNonCompatibleProjects) return false
    return true
}
