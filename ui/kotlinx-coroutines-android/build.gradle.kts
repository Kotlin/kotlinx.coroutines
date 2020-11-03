/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

configurations {
    create("r8")
}

dependencies {
    jvmMainCompileOnly("com.google.android:android:${version("android")}")
    jvmMainCompileOnly("androidx.annotation:annotation:${version("androidx_annotation")}")

    jvmTestImplementation("com.google.android:android:${version("android")}")
    jvmTestImplementation("org.robolectric:robolectric:${version("robolectric")}")
    jvmTestImplementation("org.smali:baksmali:${version("baksmali")}")

    "r8"("com.android.tools.build:builder:4.0.0-alpha06") // Contains r8-2.0.4-dev
}

val optimizedDexDir = File(buildDir, "dex-optim/")
val unOptimizedDexDir = File(buildDir, "dex-unoptim/")

val optimizedDexFile = File(optimizedDexDir, "classes.dex")
val unOptimizedDexFile = File(unOptimizedDexDir, "classes.dex")

val runR8 by tasks.registering(RunR8::class) {
    outputDex = optimizedDexDir
    inputConfig = file("testdata/r8-test-rules.pro")

    dependsOn("jvmJar")
}

val runR8NoOptim by tasks.registering(RunR8::class) {
    outputDex = unOptimizedDexDir
    inputConfig = file("testdata/r8-test-rules-no-optim.pro")

    dependsOn("jvmJar")
}

val testTasks = if (rootProject.ext.get("jvm_ir_target_enabled") as Boolean) {
    listOf(tasks.jvmTest.get(), tasks.getByName<org.jetbrains.kotlin.gradle.targets.jvm.tasks.KotlinJvmTest>("jvmIrTest"))
} else {
    listOf(tasks.jvmTest.get())
}
configure(testTasks) {
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

externalDocumentationLink(
    url = "https://developer.android.com/reference/"
)
