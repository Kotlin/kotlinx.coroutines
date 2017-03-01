/*
 * Copyright 2016-2017 JetBrains s.r.o.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

import java.io.*

const val DIRECTIVE_START = "<!--- "
const val DIRECTIVE_END = "-->"

const val TOC_DIRECTIVE = "TOC"
const val KNIT_DIRECTIVE = "KNIT"
const val INCLUDE_DIRECTIVE = "INCLUDE"
const val CLEAR_DIRECTIVE = "CLEAR"
const val TEST_DIRECTIVE = "TEST"

const val TEST_OUT_DIRECTIVE = "TEST_OUT"

const val SITE_ROOT_DIRECTIVE = "SITE_ROOT"
const val DOCS_ROOT_DIRECTIVE = "DOCS_ROOT"
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

val API_REF_REGEX = Regex("(^|[ \\]])\\[([A-Za-z0-9_.]+)\\]($|[^\\[\\(])")

fun main(args: Array<String>) {
    if (args.isEmpty()) {
        println("Usage: Knit <markdown-files>")
        return
    }
    args.forEach(::knit)
}

fun knit(markdownFileName: String) {
    println("*** Reading $markdownFileName")
    val markdownFile = File(markdownFileName)
    val toc = arrayListOf<String>()
    var knitRegex: Regex? = null
    val includes = arrayListOf<Include>()
    val code = arrayListOf<String>()
    val test = arrayListOf<String>()
    var testOut: PrintWriter? = null
    var lastPgk: String? = null
    val files = mutableSetOf<String>()
    val allApiRefs = arrayListOf<ApiRef>()
    val remainingApiRefNames = mutableSetOf<String>()
    var siteRoot: String? = null
    var docsRoot: String? = null
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
                    require(!directive.param.isEmpty()) { "$INCLUDE_DIRECTIVE directive must include regex parameter" }
                    val include = Include(Regex(directive.param))
                    if (directive.singleLine) {
                        include.lines += code
                        code.clear()
                    } else {
                        readUntilTo(DIRECTIVE_END, include.lines)
                    }
                    includes += include
                    continue@mainLoop
                }
                CLEAR_DIRECTIVE -> {
                    requireSingleLine(directive)
                    require(directive.param.isEmpty()) { "$CLEAR_DIRECTIVE directive must not have parameters" }
                    code.clear()
                    continue@mainLoop
                }
                TEST_OUT_DIRECTIVE -> {
                    require(!directive.param.isEmpty()) { "$TEST_OUT_DIRECTIVE directive must include file name parameter" }
                    val file = File(directive.param)
                    file.parentFile?.mkdirs()
                    closeTestOut(testOut)
                    println("Writing tests to ${directive.param}")
                    testOut = PrintWriter(file)
                    readUntil(DIRECTIVE_END).forEach { testOut!!.println(it) }
                }
                TEST_DIRECTIVE -> {
                    require(lastPgk != null) { "'$PACKAGE_PREFIX' prefix was not found in emitted code"}
                    require(testOut != null) { "$TEST_OUT_DIRECTIVE directive was not specified" }
                    var predicate = directive.param
                    if (test.isEmpty()) {
                        if (directive.singleLine) {
                            require(!predicate.isEmpty()) { "$TEST_OUT_DIRECTIVE must be preceded by $TEST_START block or contain test predicate"}
                        } else
                            test += readUntil(DIRECTIVE_END)
                    } else {
                        requireSingleLine(directive)
                    }
                    writeTest(testOut!!, lastPgk!!, test, predicate)
                    test.clear()
                }
                SITE_ROOT_DIRECTIVE -> {
                    requireSingleLine(directive)
                    siteRoot = directive.param
                }
                DOCS_ROOT_DIRECTIVE -> {
                    requireSingleLine(directive)
                    docsRoot = directive.param
                }
                INDEX_DIRECTIVE -> {
                    requireSingleLine(directive)
                    require(siteRoot != null) { "$SITE_ROOT_DIRECTIVE must be specified" }
                    require(docsRoot != null) { "$DOCS_ROOT_DIRECTIVE must be specified" }
                    val indexLines = processApiIndex(siteRoot!!, docsRoot!!, directive.param, remainingApiRefNames)
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
                require(test.isEmpty()) { "Previous test was not emitted with $TEST_DIRECTIVE" }
                code += ""
                readUntilTo(CODE_END, code)
                continue@mainLoop
            }
            if (inLine.startsWith(TEST_START)) {
                require(test.isEmpty()) { "Previous test was not emitted with $TEST_DIRECTIVE" }
                readUntilTo(TEST_END, test)
                continue@mainLoop
            }
            if (inLine.startsWith(SECTION_START) && markdownPart == MarkdownPart.POST_TOC) {
                val i = inLine.indexOf(' ')
                require(i >= 2) { "Invalid section start" }
                val name = inLine.substring(i + 1).trim()
                toc += "  ".repeat(i - 2) + "* [$name](#${makeSectionRef(name)})"
                continue@mainLoop
            }
            for (match in API_REF_REGEX.findAll(inLine)) {
                val apiRef = ApiRef(lineNumber, match.groups[2]!!.value)
                allApiRefs += apiRef
                remainingApiRefNames += apiRef.name
            }
            knitRegex?.find(inLine)?.let { knitMatch ->
                val fileName = knitMatch.groups[1]!!.value
                require(files.add(fileName)) { "Duplicate file name: $fileName"}
                println("Knitting $fileName ...")
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
                outLines += code
                code.clear()
                val file = File(fileName)
                val oldLines = try { file.readLines() } catch (e: IOException) { emptyList<String>() }
                if (outLines != oldLines) writeLines(file, outLines)
            }
        }
    }
    // close test output
    closeTestOut(testOut)
    // update markdown file with toc
    val newLines = buildList<String> {
        addAll(markdown.preTocText)
        if (!toc.isEmpty()) {
            add("")
            addAll(toc)
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
}

fun writeTest(testOut: PrintWriter, pgk: String, test: List<String>, predicate: String) {
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
    with (testOut) {
        println()
        println("    @Test")
        println("    fun test$funName() {")
        print  ("        test { $pgk.main(emptyArray()) }")
        when (predicate) {
            "" -> writeTestLines("verifyLines", test)
            STARTS_WITH_PREDICATE -> writeTestLines("verifyLinesStartWith", test)
            ARBITRARY_TIME_PREDICATE -> writeTestLines("verifyLinesArbitraryTime", test)
            FLEXIBLE_TIME_PREDICATE -> writeTestLines("verifyLinesFlexibleTime", test)
            FLEXIBLE_THREAD_PREDICATE -> writeTestLines("verifyLinesFlexibleThread", test)
            LINES_START_UNORDERED_PREDICATE -> writeTestLines("verifyLinesStartUnordered", test)
            LINES_START_PREDICATE -> writeTestLines("verifyLinesStart", test)
            else -> {
                println(".also { lines ->")
                println("            check($predicate)")
                println("        }")
            }
        }
        println("    }")
    }
}

private fun PrintWriter.writeTestLines(method: String, test: List<String>) {
    println(".$method(")
    for ((index, testLine) in test.withIndex()) {
        val commaOpt = if (index < test.size - 1) "," else ""
        val escapedLine = testLine.replace("\"", "\\\"")
        println("            \"$escapedLine\"$commaOpt")
    }
    println("        )")
}

private fun makeReplacements(line: String, match: MatchResult): String {
    var result = line
    for ((id, group) in match.groups.withIndex()) {
        if (group != null)
            result = result.replace("\$\$$id", group.value)
    }
    return result
}

private fun closeTestOut(testOut: PrintWriter?) {
    if (testOut != null) {
        testOut.println("}")
        testOut.close()
    }
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

fun <T : LineNumberReader> File.withLineNumberReader(factory: (Reader) -> T, block: T.() -> Unit): T {
    val reader = factory(reader())
    reader.use {
        try {
            it.block()
        } catch (e: IllegalArgumentException) {
            println("ERROR: ${this@withLineNumberReader}: ${it.lineNumber}: ${e.message}")
        }
    }
    return reader
}

fun File.withMarkdownTextReader(block: MarkdownTextReader.() -> Unit): MarkdownTextReader =
    withLineNumberReader<MarkdownTextReader>(::MarkdownTextReader, block)

fun writeLines(file: File, lines: List<String>) {
    println(" Writing $file ...")
    file.parentFile?.mkdirs()
    file.printWriter().use { out ->
        lines.forEach { out.println(it) }
    }
}

data class ApiIndexKey(
    val docsRoot: String,
    val pkg: String
)

val apiIndexCache: MutableMap<ApiIndexKey, Map<String, String>> = HashMap()

val REF_LINE_REGEX = Regex("<a href=\"([a-z/.\\-]+)\">([a-zA-z.]+)</a>")
val INDEX_HTML = "/index.html"
val INDEX_MD = "/index.md"

fun loadApiIndex(
    docsRoot: String,
    path: String,
    pkg: String,
    namePrefix: String = ""
): Map<String, String> {
    val fileName = docsRoot + "/" + path + INDEX_MD
    println("Reading index from $fileName")
    val visited = mutableSetOf<String>()
    val map = HashMap<String,String>()
    File(fileName).withLineNumberReader<LineNumberReader>(::LineNumberReader) {
        while (true) {
            val line = readLine() ?: break
            val result = REF_LINE_REGEX.matchEntire(line) ?: continue
            val refLink = result.groups[1]!!.value
            if (refLink.startsWith("..")) continue // ignore cross-references
            val refName = namePrefix + result.groups[2]!!.value
            map.put(refName, path + "/" + refLink)
            map.put(pkg + "." + refName, path + "/" + refLink)
            if (refLink.endsWith(INDEX_HTML)) {
                if (visited.add(refLink)) {
                    val path2 = path + "/" + refLink.substring(0, refLink.length - INDEX_HTML.length)
                    map += loadApiIndex(docsRoot, path2, pkg, refName + ".")
                }
            }
        }
    }
    return map
}

fun processApiIndex(
    siteRoot: String,
    docsRoot: String,
    pkg: String,
    remainingApiRefNames: MutableSet<String>
): List<String> {
    val key = ApiIndexKey(docsRoot, pkg)
    val map = apiIndexCache.getOrPut(key, { loadApiIndex(docsRoot, pkg, pkg) })
    val indexList = arrayListOf<String>()
    val it = remainingApiRefNames.iterator()
    while (it.hasNext()) {
        val refName = it.next()
        val refLink = map[refName] ?: continue
        indexList += "[$refName]: $siteRoot/$refLink"
        it.remove()
    }
    return indexList
}
