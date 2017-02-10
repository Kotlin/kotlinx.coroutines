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

import java.io.File
import java.io.IOException
import java.io.LineNumberReader
import java.io.Reader

val DIRECTIVE_START = "<!--- "
val DIRECTIVE_END = "-->"

val TOC_DIRECTIVE = "TOC"
val KNIT_DIRECTIVE = "KNIT"
val INCLUDE_DIRECTIVE = "INCLUDE"
val CLEAR_DIRECTIVE = "CLEAR"

val SITE_ROOT_DIRECTIVE = "SITE_ROOT"
val DOCS_ROOT_DIRECTIVE = "DOCS_ROOT"
val INDEX_DIRECTIVE = "INDEX"

val CODE_START = "```kotlin"
val CODE_END = "```"

val SECTION_START = "##"

val API_REF_REGEX = Regex("(^|[ \\]])\\[([A-Za-z0-9_.]+)\\]($|[^\\[\\(])")

fun main(args: Array<String>) {
    if(args.size != 1) {
        println("Usage: Knit <markdown-file>")
        return
    }
    val markdownFile = File(args[0])
    val toc = arrayListOf<String>()
    var knitRegex: Regex? = null
    val includes = arrayListOf<Include>()
    val code = arrayListOf<String>()
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
                    require(directive.param.isEmpty()) { "TOC directive must not have parameters" }
                    require(markdownPart == MarkdownPart.PRE_TOC) { "Only one TOC directive is supported" }
                    markdownPart = MarkdownPart.TOC
                }
                KNIT_DIRECTIVE -> {
                    requireSingleLine(directive)
                    require(!directive.param.isEmpty()) { "KNIT directive must include regex parameter" }
                    require(knitRegex == null) { "Only one KNIT directive is supported"}
                    knitRegex = Regex("\\((" + directive.param + ")\\)")
                    continue@mainLoop
                }
                INCLUDE_DIRECTIVE -> {
                    require(!directive.param.isEmpty()) { "INCLUDE directive must include regex parameter" }
                    val include = Include(Regex(directive.param))
                    if (directive.singleLine) {
                        include.lines += code
                        code.clear()
                    } else {
                        while (true) {
                            val includeLine = readLine() ?: break
                            if (includeLine.startsWith(DIRECTIVE_END)) break
                            include.lines += includeLine
                        }
                    }
                    includes += include
                    continue@mainLoop
                }
                CLEAR_DIRECTIVE -> {
                    requireSingleLine(directive)
                    require(directive.param.isEmpty()) { "CLEAR directive must not have parameters" }
                    code.clear()
                    continue@mainLoop
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
                    val indexLines = readApiIndex(directive.param, remainingApiRefNames, siteRoot!!, docsRoot!!)
                    skip = true
                    while (true) {
                        val skipLine = readLine() ?: break@mainLoop
                        if (directive(skipLine) != null) {
                            putBackLine = skipLine
                            break
                        }
                    }
                    skip = false
                    postTocText += indexLines
                    postTocText += putBackLine!!
                }
            }
            if (inLine.startsWith(CODE_START)) {
                code += ""
                while (true) {
                    val codeLine = readLine() ?: break
                    if (codeLine.startsWith(CODE_END)) break
                    code += codeLine
                }
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
                        var toOutLine = includeLine
                        for ((id, group) in includeMatch.groups.withIndex()) {
                            if (group != null)
                                toOutLine = toOutLine.replace("\$\$$id", group.value)
                        }
                        outLines += toOutLine
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
    // update markdown file with toc
    val newLines = markdown.preTocText + "" + toc + "" + markdown.postTocText
    if (newLines != markdown.allText) writeLines(markdownFile, newLines)
    // check apiRefs
    for (apiRef in allApiRefs) {
        if (apiRef.name in remainingApiRefNames) {
            println("WARNING: $markdownFile: ${apiRef.line}: Broken reference to [${apiRef.name}]")
        }
    }
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
    val allText = arrayListOf<String>()
    val preTocText = arrayListOf<String>()
    val postTocText = arrayListOf<String>()
    var markdownPart: MarkdownPart = MarkdownPart.PRE_TOC
    var skip = false

    override fun readLine(): String? {
        val line = super.readLine() ?: return null
        allText += line
        if (!skip) {
            when (markdownPart) {
                MarkdownPart.PRE_TOC -> preTocText += line
                MarkdownPart.POST_TOC -> postTocText += line
                MarkdownPart.TOC -> {
                } // do nothing
            }
        }
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

val REF_LINE_REGEX = Regex("<a href=\"([a-z/.\\-]+)\">([a-zA-z.]+)</a>")
val INDEX_HTML = "/index.html"
val INDEX_MD = "/index.md"

fun readApiIndex(
        path: String,
        remainingApiRefNames: MutableSet<String>,
        siteRoot: String,
        docsRoot: String,
        prefix: String = ""
): List<String> {
    val fileName = docsRoot + "/" + path + INDEX_MD
    println("Reading index from $fileName")
    val indexList = arrayListOf<String>()
    val visited = mutableSetOf<String>()
    File(fileName).withLineNumberReader<LineNumberReader>(::LineNumberReader) {
        while (true) {
            val line = readLine() ?: break
            val result = REF_LINE_REGEX.matchEntire(line) ?: continue
            val refLink = result.groups[1]!!.value
            if (refLink.startsWith("..")) continue // ignore cross-references
            val refName = prefix + result.groups[2]!!.value
            if (remainingApiRefNames.remove(refName)) {
                indexList += "[$refName]: $siteRoot/$path/$refLink"
            }
            if (refLink.endsWith(INDEX_HTML)) {
                if (visited.add(refLink)) {
                    val path2 = path + "/" + refLink.substring(0, refLink.length - INDEX_HTML.length)
                    indexList += readApiIndex(path2, remainingApiRefNames, siteRoot, docsRoot, refName + ".")
                }
            }
        }
    }
    return indexList
}