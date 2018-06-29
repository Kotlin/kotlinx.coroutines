/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

import java.io.File
import java.io.IOException
import java.io.LineNumberReader
import java.io.Reader
import java.util.*
import kotlin.properties.Delegates

// --- props in knit.properties

val knitProperties = ClassLoader.getSystemClassLoader()
    .getResource("knit.properties").openStream().use { Properties().apply { load(it) } }

val siteRoot = knitProperties.getProperty("site.root")!!
val moduleRoots = knitProperties.getProperty("module.roots").split(" ")
val moduleMarker = knitProperties.getProperty("module.marker")!!
val moduleDocs = knitProperties.getProperty("module.docs")!!

// --- markdown syntax

const val DIRECTIVE_START = "<!--- "
const val DIRECTIVE_END = "-->"

const val TOC_DIRECTIVE = "TOC"
const val KNIT_DIRECTIVE = "KNIT"
const val INCLUDE_DIRECTIVE = "INCLUDE"
const val CLEAR_DIRECTIVE = "CLEAR"
const val TEST_DIRECTIVE = "TEST"

const val TEST_OUT_DIRECTIVE = "TEST_OUT"

const val MODULE_DIRECTIVE = "MODULE"
const val INDEX_DIRECTIVE = "INDEX"

const val CODE_START = "```kotlin"
const val CODE_END = "```"

const val TEST_START = "```text"
const val TEST_END = "```"

const val SECTION_START = "##"

const val PACKAGE_PREFIX = "package "
const val STARTS_WITH_PREDICATE = "STARTS_WITH"
const val ARBITRARY_TIME_PREDICATE = "ARBITRARY_TIME"
const val FLEXIBLE_TIME_PREDICATE = "FLEXIBLE_TIME"
const val FLEXIBLE_THREAD_PREDICATE = "FLEXIBLE_THREAD"
const val LINES_START_UNORDERED_PREDICATE = "LINES_START_UNORDERED"
const val LINES_START_PREDICATE = "LINES_START"

val API_REF_REGEX = Regex("(^|[ \\]])\\[([A-Za-z0-9_().]+)\\]($|[^\\[\\(])")

fun main(args: Array<String>) {
    if (args.isEmpty()) {
        println("Usage: Knit <markdown-files>")
        return
    }
    args.forEach {
        if (!knit(it)) System.exit(1) // abort on first error with error exit code
    }
}

fun knit(markdownFileName: String): Boolean {
    println("*** Reading $markdownFileName")
    val markdownFile = File(markdownFileName)
    val tocLines = arrayListOf<String>()
    var knitRegex: Regex? = null
    val includes = arrayListOf<Include>()
    val codeLines = arrayListOf<String>()
    val testLines = arrayListOf<String>()
    var testOut: String? = null
    val testOutLines = arrayListOf<String>()
    var lastPgk: String? = null
    val files = mutableSetOf<File>()
    val allApiRefs = arrayListOf<ApiRef>()
    val remainingApiRefNames = mutableSetOf<String>()
    var moduleName: String by Delegates.notNull()
    var docsRoot: String by Delegates.notNull()
    // read markdown file
    var putBackLine: String? = null
    val markdown = markdownFile.withMarkdownTextReader {
        mainLoop@ while (true) {
            val inLine = putBackLine ?: readLine() ?: break
            putBackLine = null
            val directive = directive(inLine)
            if (directive != null && markdownPart == MarkdownPart.TOC) {
                markdownPart = MarkdownPart.POST_TOC
                postTocText += inLine
            }
            when (directive?.name) {
                TOC_DIRECTIVE -> {
                    requireSingleLine(directive)
                    require(directive.param.isEmpty()) { "$TOC_DIRECTIVE directive must not have parameters" }
                    require(markdownPart == MarkdownPart.PRE_TOC) { "Only one TOC directive is supported" }
                    markdownPart = MarkdownPart.TOC
                }
                KNIT_DIRECTIVE -> {
                    requireSingleLine(directive)
                    require(!directive.param.isEmpty()) { "$KNIT_DIRECTIVE directive must include regex parameter" }
                    require(knitRegex == null) { "Only one KNIT directive is supported"}
                    knitRegex = Regex("\\((" + directive.param + ")\\)")
                    continue@mainLoop
                }
                INCLUDE_DIRECTIVE -> {
                    if (directive.param.isEmpty()) {
                        require(!directive.singleLine) { "$INCLUDE_DIRECTIVE directive without parameters must not be single line" }
                        readUntilTo(DIRECTIVE_END, codeLines)
                    } else {
                        val include = Include(Regex(directive.param))
                        if (directive.singleLine) {
                            include.lines += codeLines
                            codeLines.clear()
                        } else {
                            readUntilTo(DIRECTIVE_END, include.lines)
                        }
                        includes += include
                    }
                    continue@mainLoop
                }
                CLEAR_DIRECTIVE -> {
                    requireSingleLine(directive)
                    require(directive.param.isEmpty()) { "$CLEAR_DIRECTIVE directive must not have parameters" }
                    codeLines.clear()
                    continue@mainLoop
                }
                TEST_OUT_DIRECTIVE -> {
                    require(!directive.param.isEmpty()) { "$TEST_OUT_DIRECTIVE directive must include file name parameter" }
                    flushTestOut(markdownFile.parentFile, testOut, testOutLines)
                    testOut = directive.param
                    readUntil(DIRECTIVE_END).forEach { testOutLines += it }
                }
                TEST_DIRECTIVE -> {
                    require(lastPgk != null) { "'$PACKAGE_PREFIX' prefix was not found in emitted code"}
                    require(testOut != null) { "$TEST_OUT_DIRECTIVE directive was not specified" }
                    val predicate = directive.param
                    if (testLines.isEmpty()) {
                        if (directive.singleLine) {
                            require(!predicate.isEmpty()) { "$TEST_OUT_DIRECTIVE must be preceded by $TEST_START block or contain test predicate"}
                        } else
                            testLines += readUntil(DIRECTIVE_END)
                    } else {
                        requireSingleLine(directive)
                    }
                    makeTest(testOutLines, lastPgk!!, testLines, predicate)
                    testLines.clear()
                }
                MODULE_DIRECTIVE -> {
                    requireSingleLine(directive)
                    moduleName = directive.param
                    docsRoot = findModuleRootDir(moduleName) + "/" + moduleDocs + "/" + moduleName
                }
                INDEX_DIRECTIVE -> {
                    requireSingleLine(directive)
                    val indexLines = processApiIndex(siteRoot + "/" + moduleName, docsRoot, directive.param, remainingApiRefNames)
                        ?: throw IllegalArgumentException("Failed to load index for ${directive.param}")
                    skip = true
                    while (true) {
                        val skipLine = readLine() ?: break@mainLoop
                        if (directive(skipLine) != null) {
                            putBackLine = skipLine
                            break
                        }
                    }
                    skip = false
                    outText += indexLines
                    outText += putBackLine!!
                }
            }
            if (inLine.startsWith(CODE_START)) {
                require(testOut == null || testLines.isEmpty()) { "Previous test was not emitted with $TEST_DIRECTIVE" }
                codeLines += ""
                readUntilTo(CODE_END, codeLines)
                continue@mainLoop
            }
            if (inLine.startsWith(TEST_START)) {
                require(testOut == null || testLines.isEmpty()) { "Previous test was not emitted with $TEST_DIRECTIVE" }
                readUntilTo(TEST_END, testLines)
                continue@mainLoop
            }
            if (inLine.startsWith(SECTION_START) && markdownPart == MarkdownPart.POST_TOC) {
                val i = inLine.indexOf(' ')
                require(i >= 2) { "Invalid section start" }
                val name = inLine.substring(i + 1).trim()
                tocLines += "  ".repeat(i - 2) + "* [$name](#${makeSectionRef(name)})"
                continue@mainLoop
            }
            for (match in API_REF_REGEX.findAll(inLine)) {
                val apiRef = ApiRef(lineNumber, match.groups[2]!!.value)
                allApiRefs += apiRef
                remainingApiRefNames += apiRef.name
            }
            knitRegex?.find(inLine)?.let { knitMatch ->
                val fileName = knitMatch.groups[1]!!.value
                val file = File(markdownFile.parentFile, fileName)
                require(files.add(file)) { "Duplicate file: $file"}
                println("Knitting $file ...")
                val outLines = arrayListOf<String>()
                for (include in includes) {
                    val includeMatch = include.regex.matchEntire(fileName) ?: continue
                    include.lines.forEach { includeLine ->
                        val line = makeReplacements(includeLine, includeMatch)
                        if (line.startsWith(PACKAGE_PREFIX))
                            lastPgk = line.substring(PACKAGE_PREFIX.length).trim()
                        outLines += line
                    }
                }
                outLines += codeLines
                codeLines.clear()
                writeLinesIfNeeded(file, outLines)
            }
        }
    } ?: return false // false when failed
    // update markdown file with toc
    val newLines = buildList<String> {
        addAll(markdown.preTocText)
        if (!tocLines.isEmpty()) {
            add("")
            addAll(tocLines)
            add("")
        }
        addAll(markdown.postTocText)
    }
    if (newLines != markdown.inText) writeLines(markdownFile, newLines)
    // check apiRefs
    for (apiRef in allApiRefs) {
        if (apiRef.name in remainingApiRefNames) {
            println("WARNING: $markdownFile: ${apiRef.line}: Broken reference to [${apiRef.name}]")
        }
    }
    // write test output
    flushTestOut(markdownFile.parentFile, testOut, testOutLines)
    return true
}

fun makeTest(testOutLines: MutableList<String>, pgk: String, test: List<String>, predicate: String) {
    val funName = buildString {
        var cap = true
        for (c in pgk) {
            if (c == '.') {
                cap = true
            } else {
                append(if (cap) c.toUpperCase() else c)
                cap = false
            }
        }
    }
    testOutLines += ""
    testOutLines += "    @Test"
    testOutLines += "    fun test$funName() {"
    val prefix = "        test(\"$funName\") { $pgk.main(emptyArray()) }"
    when (predicate) {
        "" -> makeTestLines(testOutLines, prefix, "verifyLines", test)
        STARTS_WITH_PREDICATE -> makeTestLines(testOutLines, prefix, "verifyLinesStartWith", test)
        ARBITRARY_TIME_PREDICATE -> makeTestLines(testOutLines, prefix, "verifyLinesArbitraryTime", test)
        FLEXIBLE_TIME_PREDICATE -> makeTestLines(testOutLines, prefix, "verifyLinesFlexibleTime", test)
        FLEXIBLE_THREAD_PREDICATE -> makeTestLines(testOutLines, prefix, "verifyLinesFlexibleThread", test)
        LINES_START_UNORDERED_PREDICATE -> makeTestLines(testOutLines, prefix, "verifyLinesStartUnordered", test)
        LINES_START_PREDICATE -> makeTestLines(testOutLines, prefix, "verifyLinesStart", test)
        else -> {
            testOutLines += prefix +  ".also { lines ->"
            testOutLines += "            check($predicate)"
            testOutLines += "        }"
        }
    }
    testOutLines += "    }"
}

private fun makeTestLines(testOutLines: MutableList<String>, prefix: String, method: String, test: List<String>) {
    testOutLines += "$prefix.$method("
    for ((index, testLine) in test.withIndex()) {
        val commaOpt = if (index < test.size - 1) "," else ""
        val escapedLine = testLine.replace("\"", "\\\"")
        testOutLines += "            \"$escapedLine\"$commaOpt"
    }
    testOutLines += "        )"
}

private fun makeReplacements(line: String, match: MatchResult): String {
    var result = line
    for ((id, group) in match.groups.withIndex()) {
        if (group != null)
            result = result.replace("\$\$$id", group.value)
    }
    return result
}

private fun flushTestOut(parentDir: File?, testOut: String?, testOutLines: MutableList<String>) {
    if (testOut == null) return
    val file = File(parentDir, testOut)
    testOutLines += "}"
    writeLinesIfNeeded(file, testOutLines)
    testOutLines.clear()
}

private fun MarkdownTextReader.readUntil(marker: String): List<String> =
    arrayListOf<String>().also { readUntilTo(marker, it) }

private fun MarkdownTextReader.readUntilTo(marker: String, list: MutableList<String>) {
    while (true) {
        val line = readLine() ?: break
        if (line.startsWith(marker)) break
        list += line
    }
}

private inline fun <T> buildList(block: ArrayList<T>.() -> Unit): List<T> {
    val result = arrayListOf<T>()
    result.block()
    return result
}

private fun requireSingleLine(directive: Directive) {
    require(directive.singleLine) { "${directive.name} directive must end on the same line with '$DIRECTIVE_END'" }
}

fun makeSectionRef(name: String): String = name.replace(' ', '-').replace(".", "").toLowerCase()

class Include(val regex: Regex, val lines: MutableList<String> = arrayListOf())

class Directive(
    val name: String,
    val param: String,
    val singleLine: Boolean
)

fun directive(line: String): Directive? {
    if (!line.startsWith(DIRECTIVE_START)) return null
    var s = line.substring(DIRECTIVE_START.length).trim()
    val singleLine = s.endsWith(DIRECTIVE_END)
    if (singleLine) s = s.substring(0, s.length - DIRECTIVE_END.length)
    val i = s.indexOf(' ')
    val name = if (i < 0) s else s.substring(0, i)
    val param = if (i < 0) "" else s.substring(i).trim()
    return Directive(name, param, singleLine)
}

class ApiRef(val line: Int, val name: String)

enum class MarkdownPart { PRE_TOC, TOC, POST_TOC }

class MarkdownTextReader(r: Reader) : LineNumberReader(r) {
    val inText = arrayListOf<String>()
    val preTocText = arrayListOf<String>()
    val postTocText = arrayListOf<String>()
    var markdownPart: MarkdownPart = MarkdownPart.PRE_TOC
    var skip = false

    val outText: MutableList<String> get() = when (markdownPart) {
        MarkdownPart.PRE_TOC -> preTocText
        MarkdownPart.POST_TOC -> postTocText
        else -> throw IllegalStateException("Wrong state: $markdownPart")
    }

    override fun readLine(): String? {
        val line = super.readLine() ?: return null
        inText += line
        if (!skip && markdownPart != MarkdownPart.TOC)
            outText += line
        return line
    }
}

fun <T : LineNumberReader> File.withLineNumberReader(factory: (Reader) -> T, block: T.() -> Unit): T? {
    val reader = factory(reader())
    reader.use {
        try {
            it.block()
        } catch (e: Exception) {
            println("ERROR: ${this@withLineNumberReader}: ${it.lineNumber}: ${e.message}")
            return null
        }
    }
    return reader
}

fun File.withMarkdownTextReader(block: MarkdownTextReader.() -> Unit): MarkdownTextReader? =
    withLineNumberReader<MarkdownTextReader>(::MarkdownTextReader, block)

fun writeLinesIfNeeded(file: File, outLines: List<String>) {
    val oldLines = try {
        file.readLines()
    } catch (e: IOException) {
        emptyList<String>()
    }
    if (outLines != oldLines) writeLines(file, outLines)
}

fun writeLines(file: File, lines: List<String>) {
    println(" Writing $file ...")
    file.parentFile?.mkdirs()
    file.printWriter().use { out ->
        lines.forEach { out.println(it) }
    }
}

fun findModuleRootDir(name: String): String =
    moduleRoots
        .map { "$it/$name" }
        .firstOrNull { File("$it/$moduleMarker").exists() }
        ?: throw IllegalArgumentException("Module $name is not found in any of the module root dirs")

data class ApiIndexKey(
    val docsRoot: String,
    val pkg: String
)

val apiIndexCache: MutableMap<ApiIndexKey, Map<String, List<String>>> = HashMap()

val REF_LINE_REGEX = Regex("<a href=\"([a-z/.\\-]+)\">([a-zA-z.]+)</a>")
val INDEX_HTML = "/index.html"
val INDEX_MD = "/index.md"
val FUNCTIONS_SECTION_HEADER = "### Functions"

fun HashMap<String, MutableList<String>>.putUnambiguous(key: String, value: String) {
    val oldValue = this[key]
    if (oldValue != null) {
        oldValue.add(value)
        put(key, oldValue)
    } else {
        put(key, mutableListOf(value))
    }
}

fun loadApiIndex(
    docsRoot: String,
    path: String,
    pkg: String,
    namePrefix: String = ""
): Map<String, MutableList<String>>? {
    val fileName = docsRoot + "/" + path + INDEX_MD
    val visited = mutableSetOf<String>()
    val map = HashMap<String, MutableList<String>>()
    var inFunctionsSection = false
    File(fileName).withLineNumberReader<LineNumberReader>(::LineNumberReader) {
        while (true) {
            val line = readLine() ?: break
            if (line == FUNCTIONS_SECTION_HEADER) inFunctionsSection = true
            val result = REF_LINE_REGEX.matchEntire(line) ?: continue
            val link = result.groups[1]!!.value
            if (link.startsWith("..")) continue // ignore cross-references
            val absLink = path + "/" + link
            var name = result.groups[2]!!.value
            // a special disambiguation fix for pseudo-constructor functions
            if (inFunctionsSection && name[0] in 'A'..'Z') name += "()"
            val refName = namePrefix + name
            val fqName = pkg + "." + refName
            // Put short names for extensions on 3rd party classes (prefix is FQname of those classes)
            if (namePrefix != "" && namePrefix[0] in 'a'..'z') map.putUnambiguous(name, absLink)
            // Always put fully qualified names
            map.putUnambiguous(refName, absLink)
            map.putUnambiguous(fqName, absLink)
            if (link.endsWith(INDEX_HTML)) {
                if (visited.add(link)) {
                    val path2 = path + "/" + link.substring(0, link.length - INDEX_HTML.length)
                    map += loadApiIndex(docsRoot, path2, pkg, refName + ".")
                        ?: throw IllegalArgumentException("Failed to parse ${docsRoot + "/" + path2}")
                }
            }
        }
    } ?: return null // return null on failure
    return map
}

fun processApiIndex(
    siteRoot: String,
    docsRoot: String,
    pkg: String,
    remainingApiRefNames: MutableSet<String>
): List<String>? {
    val key = ApiIndexKey(docsRoot, pkg)
    val map = apiIndexCache.getOrPut(key, {
        print("Parsing API docs at $docsRoot/$pkg: ")
        val result = loadApiIndex(docsRoot, pkg, pkg) ?: return null // null on failure
        println("${result.size} definitions")
        result
    })
    val indexList = arrayListOf<String>()
    val it = remainingApiRefNames.iterator()
    while (it.hasNext()) {
        val refName = it.next()
        val refLink = map[refName] ?: continue
        if (refLink.size > 1) {
            println("INFO: Ambiguous reference to [$refName]: $refLink, taking the shortest one")
        }

        val link = refLink.minBy { it.length }
        indexList += "[$refName]: $siteRoot/$link"
        it.remove()
    }
    return indexList
}
