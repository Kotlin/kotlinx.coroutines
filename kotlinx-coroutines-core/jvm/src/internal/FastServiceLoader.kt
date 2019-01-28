package kotlinx.coroutines.internal

import java.util.*
import java.io.*
import java.net.*
import java.util.jar.*
import java.util.zip.*

/**
 * Name of the boolean property that enables using of [FastServiceLoader].
 */
private const val FAST_SERVICE_LOADER_PROPERTY_NAME = "kotlinx.coroutines.verify.service.loader"

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

    @JvmField
    internal val FAST_SERVICE_LOADER_ENABLED = systemProp(FAST_SERVICE_LOADER_PROPERTY_NAME, true)

    internal fun <S> load(service: Class<S>, loader: ClassLoader): List<S> {
        if (!FAST_SERVICE_LOADER_ENABLED) {
            return ServiceLoader.load(service, loader).toList()
        }
        return try {
            loadProviders(service, loader)
        } catch (e: Throwable) {
            // Fallback to default service loader
            ServiceLoader.load(service, loader).toList()
        }
    }

    internal fun <S> loadProviders(service: Class<S>, loader: ClassLoader): List<S> {
        val fullServiceName = PREFIX + service.name
        val urls = loader.getResources(fullServiceName).toList()
        val providers = mutableListOf<S>()
        urls.forEach {
            val providerNames = parse(it)
            providers.addAll(providerNames.map { getProviderInstance(it, loader, service) })
        }
        require(providers.isNotEmpty()) { "No providers were loaded with FastServiceLoader" }
        return providers
    }

    private fun <S> getProviderInstance(name: String, loader: ClassLoader, service: Class<S>): S {
        val clazz = Class.forName(name, false, loader)
        require(service.isAssignableFrom(clazz)) { "Expected service of class $service, but found $clazz" }
        return service.cast(clazz.getDeclaredConstructor().newInstance())
    }

    private fun parse(url: URL): List<String> {
        val string = url.toString()
        return if (string.startsWith("jar")) {
            val pathToJar = string.substringAfter("jar:file:").substringBefore('!')
            val entry = string.substringAfter("!/")
            (JarFile(pathToJar, false) as Closeable).use { file ->
                BufferedReader(InputStreamReader((file as JarFile).getInputStream(ZipEntry(entry)),"UTF-8")).use { r ->
                    parseFile(r)
                }
            }
        } else emptyList()
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
