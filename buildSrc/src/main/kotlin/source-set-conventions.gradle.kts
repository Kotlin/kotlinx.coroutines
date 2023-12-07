/*
 * Copyright 2016-2023 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */
import org.jetbrains.kotlin.gradle.dsl.*

// Redefine source sets because we are not using 'kotlin/main/fqn' folder convention
// TODO: port benchmarks to the same scheme
configure(subprojects.filter { !sourceless.contains(it.name) && it.name != "benchmarks" }) {
    kotlinExtension.sourceSets.forEach {
        it.configureDirectoryPaths()
    }
}
