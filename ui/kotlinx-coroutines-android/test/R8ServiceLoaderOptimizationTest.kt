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
import kotlin.test.assertEquals

class R8ServiceLoaderOptimizationTest {
  private val r8Dex = File(System.getProperty("dexPath")!!).asDexFile()

  @Test fun noServiceLoaderCalls() {
    val serviceLoaderInvocations = r8Dex.classes
        // Create a map of type names to a list of their ServiceLoader invocations.
        .associate { clz ->
          clz.type to clz.toSmali().lines().filter { "Ljava/util/ServiceLoader;->" in it }
        }
        .filterValues { it.isNotEmpty() }
    assertEquals(emptyMap(), serviceLoaderInvocations)
  }
}

private fun File.asDexFile(): DexFile = DexFileFactory.loadDexFile(this, null)

private fun ClassDef.toSmali(): String {
  val stringWriter = StringWriter()
  ClassDefinition(BaksmaliOptions(), this).writeTo(IndentingWriter(stringWriter))
  return stringWriter.toString()
}
