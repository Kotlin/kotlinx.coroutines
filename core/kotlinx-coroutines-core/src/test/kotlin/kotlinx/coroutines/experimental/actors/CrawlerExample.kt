package kotlinx.coroutines.experimental.actors

import io.ktor.client.*
import io.ktor.client.engine.apache.*
import io.ktor.client.request.*
import kotlinx.coroutines.experimental.*
import org.jsoup.*
import java.net.*
import kotlin.system.*


class Crawler(private val initialUrl: String, private val maxDepth: Int) : TypedActor<Crawler>() {

    private val extractor: UrlExtractor
    private val downloader: Downloader

    init {
        val httpClient = HttpClient(Apache)
        extractor = concurrent(parallelism = 8, parent = this) { UrlExtractor(this) }
        downloader = concurrent(parallelism = 512, parent = this) { Downloader(this, httpClient, extractor) }
    }

    private val index: MutableMap<String, Int> = mutableMapOf()
    private val visitedUrls = mutableSetOf<String>()
    private var inFlightRequests = 0

    suspend fun start() {
        ++inFlightRequests
        downloader.download(initialUrl, 0)
    }

    suspend fun urlExtracted(baseUrl: String, extractedUrl: String, depth: Int): Unit = act {
        updateIndex(baseUrl, extractedUrl)
        if (depth < maxDepth && visitedUrls.add(extractedUrl)) {
            ++inFlightRequests
            downloader.download(extractedUrl, depth + 1)
        }
    }

    suspend fun urlProcessed() = act {
        tryFinish()
    }

    suspend fun onUrlError(url: String, e: Exception) = act {
        println("Failed to download url $url: $e")
        tryFinish()
    }

    private fun tryFinish() {
        if (--inFlightRequests == 0) {
            val top10 = index.toList().sortedBy { (_, value) -> -value }.take(10).toMap()
            println("Finished crawling, index: $top10")
            close() // Note that on close() all children will be closed as well
        }
    }

    private fun updateIndex(baseUrl: String, extractedUrl: String) {
        try {
            val baseHost = URL(baseUrl).host.removePrefix("www.")
            val extractedHost = URL(extractedUrl).host.removePrefix("www.")
            if (baseHost != extractedHost) {
                val counter = index[extractedHost] ?: 0
                index[extractedHost] = counter + 1
            }
        } catch (e: Exception) {
            println("Index is not updated, base url: $baseUrl, extracted url: $extractedUrl: $e")
        }
    }
}

class Downloader(
    private val crawler: Crawler,
    private val client: HttpClient,
    private val extractor: UrlExtractor
) : TypedActor<Downloader>() {

    suspend fun download(url: String, depth: Int) = act {
        try {
            val htmlContent = client.get<String>(url)
            extractor.extractUrls(url, htmlContent, depth)
        } catch (e: Exception) {
            crawler.onUrlError(url, e)
        }
    }

    override fun onClose() = client.close() // close is idempotent
}

class UrlExtractor(private val crawler: Crawler) : TypedActor<UrlExtractor>() {

    suspend fun extractUrls(baseUrl: String, htmlContent: String, depth: Int): Unit = act {
        Jsoup.parse(htmlContent, baseUrl).select("a[href]")
            .asSequence()
            .map { it.absUrl("href") }
            .filter { !it.contains("mailto:") && it.isNotEmpty() }
            .forEach { crawler.urlExtracted(baseUrl, it, depth) }
        // TODO: finally ?
        crawler.urlProcessed()
    }
}

fun main(args: Array<String>) = runBlocking {
    val crawler = Crawler("https://news.ycombinator.com/", 1)
    val elapsedSeconds = measureTimeMillis {
        crawler.start()
        crawler.join()
    } / 1000

    println("Elapsed $elapsedSeconds seconds")
}
