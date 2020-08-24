/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

import org.jetbrains.dokka.DokkaConfiguration.ExternalDocumentationLink
import org.jetbrains.dokka.gradle.DokkaTask
import java.net.URL

configurations {
    create("r8")
}

dependencies {
    compileOnly("com.google.android:android:${version("android")}")
    compileOnly("androidx.annotation:annotation:${version("androidx_annotation")}")

    testImplementation("com.google.android:android:${version("android")}")
    testImplementation("org.robolectric:robolectric:${version("robolectric")}")
    testImplementation("org.smali:baksmali:${version("baksmali")}")

    "r8"("com.android.tools.build:builder:4.0.0-alpha06") // Contains r8-2.0.4-dev
}

open class RunR8Task : JavaExec() {

    @OutputDirectory
    lateinit var outputDex: File

    @InputFile
    lateinit var inputConfig: File

    @InputFile
    val inputConfigCommon: File = File("testdata/r8-test-common.pro")

    @InputFiles
    val jarFile: File = project.tasks.named<Zip>("jar").get().archivePath

    init {
        classpath = project.configurations["r8"]
        main = "com.android.tools.r8.R8"
    }

    override fun exec() {
        // Resolve classpath only during execution
        val arguments = mutableListOf(
            "--release",
            "--no-desugaring",
            "--output", outputDex.absolutePath,
            "--pg-conf", inputConfig.absolutePath
        )
        arguments.addAll(project.configurations.runtimeClasspath.files.map { it.absolutePath })
        arguments.add(jarFile.absolutePath)

        args = arguments

        project.delete(outputDex)
        outputDex.mkdirs()

        super.exec()
    }
}

val optimizedDexDir = File(buildDir, "dex-optim/")
val unOptimizedDexDir = File(buildDir, "dex-unoptim/")

val optimizedDexFile = File(optimizedDexDir, "classes.dex")
val unOptimizedDexFile = File(unOptimizedDexDir, "classes.dex")

val runR8 = tasks.register<RunR8Task>("runR8") {
    outputDex = optimizedDexDir
    inputConfig = file("testdata/r8-test-rules.pro")

    dependsOn("jar")
}

val runR8NoOptim = tasks.register<RunR8Task>("runR8NoOptim") {
    outputDex = unOptimizedDexDir
    inputConfig = file("testdata/r8-test-rules-no-optim.pro")

    dependsOn("jar")
}

tasks.test {
    // Ensure the R8-processed dex is built and supply its path as a property to the test.
    dependsOn(runR8)
    dependsOn(runR8NoOptim)

    inputs.files(optimizedDexFile, unOptimizedDexFile)

    systemProperty("dexPath", optimizedDexFile.absolutePath)
    systemProperty("noOptimDexPath", unOptimizedDexFile.absolutePath)

    // Output custom metric with the size of the optimized dex
    doLast {
        println("##teamcity[buildStatisticValue key='optimizedDexSize' value='${optimizedDexFile.length()}']")
    }
}

tasks.withType<DokkaTask>().configureEach {
    externalDocumentationLink(delegateClosureOf<ExternalDocumentationLink.Builder> {
        url = URL("https://developer.android.com/reference/")
        packageListUrl = projectDir.toPath().resolve("package.list").toUri().toURL()
    })
}
