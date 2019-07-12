/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.android

import org.jf.baksmali.Adaptors.ClassDefinition
import org.jf.baksmali.BaksmaliOptions
import org.jf.dexlib2.DexFileFactory
import org.jf.dexlib2.iface.ClassDef
import org.jf.dexlib2.iface.DexFile
import org.jf.util.IndentingWriter
import org.junit.Test
import java.io.File
import java.io.StringWriter
import java.util.stream.Collectors
import kotlin.test.assertEquals

class R8ServiceLoaderOptimizationTest {
  private val r8Dex = File(System.getProperty("dexPath")!!).asDexFile()
  private val r8DexNoOptim = File(System.getProperty("noOptimDexPath")!!).asDexFile()

  @Test fun noServiceLoaderCalls() {
    val serviceLoaderInvocations = r8Dex.classes
        // Create a map of type names to a list of their ServiceLoader invocations.
        .associate { clz ->
          clz.type to clz.toSmali().lines().filter { "Ljava/util/ServiceLoader;->" in it }
        }
        .filterValues { it.isNotEmpty() }
    assertEquals(emptyMap(), serviceLoaderInvocations)
  }

  @Test fun androidDispatcherIsKept() {
    val hasAndroidDispatcher = r8DexNoOptim.classes.any {
        it.type == "Lkotlinx/coroutines/android/AndroidDispatcherFactory;"
    }

    assertEquals(true, hasAndroidDispatcher)
  }

  @Test fun noOptimRulesMatch() {
    val paths = listOf(
            "META-INF/com.android.tools/proguard/coroutines.pro",
            "META-INF/proguard/coroutines.pro",
            "META-INF/com.android.tools/r8-max-1.5.999/coroutines.pro"
    )
    paths.associate { path ->
      val ruleSet = javaClass.classLoader.getResourceAsStream(path)!!.bufferedReader().lines().filter { line ->
        line.isNotBlank() && !line.startsWith("#")
      }.collect(Collectors.toSet())
      path to ruleSet
    }.asSequence().reduce { acc: Map.Entry<String, MutableSet<String>>, entry: Map.Entry<String, MutableSet<String>> ->
      assertEquals(
              acc.value,
              entry.value,
              "Rule sets between ${acc.key} and ${entry.key} don't match."
              )
      entry
    }
  }
}

private fun File.asDexFile(): DexFile = DexFileFactory.loadDexFile(this, null)

private fun ClassDef.toSmali(): String {
  val stringWriter = StringWriter()
  ClassDefinition(BaksmaliOptions(), this).writeTo(IndentingWriter(stringWriter))
  return stringWriter.toString()
}
