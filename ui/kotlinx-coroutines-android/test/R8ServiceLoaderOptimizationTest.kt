/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.android

import org.jf.dexlib2.*
import org.junit.Test
import java.io.*
import java.util.stream.*
import kotlin.test.*

class R8ServiceLoaderOptimizationTest {
    private val r8Dex = File(System.getProperty("dexPath")!!).asDexFile()
    private val r8DexNoOptim = File(System.getProperty("noOptimDexPath")!!).asDexFile()

    @Test
    fun noServiceLoaderCalls() {
        val serviceLoaderInvocations = r8Dex.types.any {
            it.type == "Ljava/util/ServiceLoader;"
        }
        assertEquals(
                false,
                serviceLoaderInvocations,
                "References to the ServiceLoader class were found in the resulting DEX."
        )
    }

    @Test
    fun androidDispatcherIsKept() {
        val hasAndroidDispatcher = r8DexNoOptim.classes.any {
            it.type == "Lkotlinx/coroutines/android/AndroidDispatcherFactory;"
        }

        assertEquals(true, hasAndroidDispatcher)
    }

    @Test
    fun noOptimRulesMatch() {
        val paths = listOf(
                "META-INF/com.android.tools/proguard/coroutines.pro",
                "META-INF/proguard/coroutines.pro",
                "META-INF/com.android.tools/r8-upto-1.6.0/coroutines.pro"
        )
        paths.associateWith { path ->
            val ruleSet = javaClass.classLoader.getResourceAsStream(path)!!.bufferedReader().lines().filter { line ->
                line.isNotBlank() && !line.startsWith("#")
            }.collect(Collectors.toSet())
            ruleSet
        }.asSequence().reduce { acc, entry ->
            assertEquals(
                    acc.value,
                    entry.value,
                    "Rule sets between ${acc.key} and ${entry.key} don't match."
            )
            entry
        }
    }
}

private fun File.asDexFile() = DexFileFactory.loadDexFile(this, null)
