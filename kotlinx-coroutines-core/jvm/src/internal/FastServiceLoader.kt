/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.internal

import java.io.*
import java.net.*
import java.util.*
import java.util.jar.*
import java.util.zip.*
import kotlin.collections.ArrayList

/**
 * Don't use JvmField here to enable R8 optimizations via "assumenosideeffects"
 */
internal val ANDROID_DETECTED = runCatching { Class.forName("android.os.Build") }.isSuccess

/**
 * A simplified version of [ServiceLoader].
 * FastServiceLoader locates and instantiates all service providers named in configuration
 * files placed in the resource directory <tt>META-INF/services</tt>.
 *
 * The main difference between this class and classic service loader is in skipping
 * verification JARs. A verification requires reading the whole JAR (and it causes problems and ANRs on Android devices)
 * and prevents only trivial checksum issues. See #878.
 *
 * If any error occurs during loading, it fallbacks to [ServiceLoader], mostly to prevent R8 issues.
 */
internal object FastServiceLoader {
    private const val PREFIX: String = "META-INF/services/"

    /**
     * This method attempts to load [MainDispatcherFactory] in Android-friendly way.
     *
     * If we are not on Android, this method fallbacks to a regular service loading,
     * else we attempt to do `Class.forName` lookup for
     * `AndroidDispatcherFactory` and `TestMainDispatcherFactory`.
     * If lookups are successful, we return resultinAg instances because we know that
     * `MainDispatcherFactory` API is internal and this is the only possible classes of `MainDispatcherFactory` Service on Android.
     *
     * Such intricate dance is required to avoid calls to `ServiceLoader.load` for multiple reasons:
     * 1) It eliminates disk lookup on potentially slow devices on the Main thread.
     * 2) Various Android toolchain versions by various vendors don't tend to handle ServiceLoader calls properly.
     *    Sometimes META-INF is removed from the resulting APK, sometimes class names are mangled, etc.
     *    While it is not the problem of `kotlinx.coroutines`, it significantly worsens user experience, thus we are workarounding it.
     *    Examples of such issues are #932, #1072, #1557, #1567
     *
     * We also use SL for [CoroutineExceptionHandler], but we do not experience the same problems and CEH is a public API
     * that may already be injected vis SL, so we are not using the same technique for it.
     */
    internal fun loadMainDispatcherFactory(): List<MainDispatcherFactory> {
        val clz = MainDispatcherFactory::class.java
        if (!ANDROID_DETECTED) {
            return load(clz, clz.classLoader)
        }

        return try {
            val result = ArrayList<MainDispatcherFactory>(2)
            createInstanceOf(clz, "kotlinx.coroutines.android.AndroidDispatcherFactory")?.apply { result.add(this) }
            createInstanceOf(clz, "kotlinx.coroutines.test.internal.TestMainDispatcherFactory")?.apply { result.add(this) }
            result
        } catch (e: Throwable) {
            // Fallback to the regular SL in case of any unexpected exception
            load(clz, clz.classLoader)
        }
    }

    /*
     * This method is inline to have a direct Class.forName("string literal") in the byte code to avoid weird interactions with ProGuard/R8.
     */
    @Suppress("NOTHING_TO_INLINE")
    private inline fun createInstanceOf(
        baseClass: Class<MainDispatcherFactory>,
        serviceClass: String
    ): MainDispatcherFactory? {
        return try {
            val clz = Class.forName(serviceClass, true, baseClass.classLoader)
            baseClass.cast(clz.getDeclaredConstructor().newInstance())
        } catch (e: ClassNotFoundException) { // Do not fail if TestMainDispatcherFactory is not found
            null
        }
    }

    private fun <S> load(service: Class<S>, loader: ClassLoader): List<S> {
        return try {
            loadProviders(service, loader)
        } catch (e: Throwable) {
            // Fallback to default service loader
            ServiceLoader.load(service, loader).toList()
        }
    }

    // Visible for tests
    internal fun <S> loadProviders(service: Class<S>, loader: ClassLoader): List<S> {
        val fullServiceName = PREFIX + service.name
        // Filter out situations when both JAR and regular files are in the classpath (e.g. IDEA)
        val urls = loader.getResources(fullServiceName)
        val providers = urls.toList().flatMap { parse(it) }.toSet()
        require(providers.isNotEmpty()) { "No providers were loaded with FastServiceLoader" }
        return providers.map { getProviderInstance(it, loader, service) }
    }

    private fun <S> getProviderInstance(name: String, loader: ClassLoader, service: Class<S>): S {
        val clazz = Class.forName(name, false, loader)
        require(service.isAssignableFrom(clazz)) { "Expected service of class $service, but found $clazz" }
        return service.cast(clazz.getDeclaredConstructor().newInstance())
    }

    private fun parse(url: URL): List<String> {
        val path = url.toString()
        // Fast-path for JARs
        if (path.startsWith("jar")) {
            val pathToJar = path.substringAfter("jar:file:").substringBefore('!')
            val entry = path.substringAfter("!/")
            // mind the verify = false flag!
            (JarFile(pathToJar, false)).use { file ->
                BufferedReader(InputStreamReader(file.getInputStream(ZipEntry(entry)), "UTF-8")).use { r ->
                    return parseFile(r)
                }
            }
        }
        // Regular path for everything else
        return BufferedReader(InputStreamReader(url.openStream())).use { reader ->
            parseFile(reader)
        }
    }

    // JarFile does no implement Closesable on Java 1.6
    private inline fun <R> JarFile.use(block: (JarFile) -> R): R {
        var cause: Throwable? = null
        try {
            return block(this)
        } catch (e: Throwable) {
            cause = e
            throw e
        } finally {
            try {
                close()
            } catch (closeException: Throwable) {
                if (cause === null) throw closeException
                cause.addSuppressed(closeException)
                throw cause
            }
        }
    }

    private fun parseFile(r: BufferedReader): List<String> {
        val names = mutableSetOf<String>()
        while (true) {
            val line = r.readLine() ?: break
            val serviceName = line.substringBefore("#").trim()
            require(serviceName.all { it == '.' || Character.isJavaIdentifierPart(it) }) { "Illegal service provider class name: $serviceName" }
            if (serviceName.isNotEmpty()) {
                names.add(serviceName)
            }
        }
        return names.toList()
    }
}
