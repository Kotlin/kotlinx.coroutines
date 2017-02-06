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

val CODE_START = "```kotlin"
val CODE_END = "```"

val SECTION_START = "##"

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
    // read markdown file
    val markdown = markdownFile.withMarkdownTextReader {
        mainLoop@ while (true) {
            val inLine = readLine() ?: break
            val directive = directive(inLine)
            if (directive != null && markdownPart == MarkdownPart.TOC) {
                markdownPart = MarkdownPart.POST_TOC
                postTocText += inLine
            }
            when (directive?.name) {
                TOC_DIRECTIVE -> {
                    require(directive.singleLine) { "TOC directive must end on the same line with '$DIRECTIVE_END'" }
                    require(directive.param.isEmpty()) { "TOC directive must not have parameters" }
                    require(markdownPart == MarkdownPart.PRE_TOC) { "Only one TOC directive is supported" }
                    markdownPart = MarkdownPart.TOC
                }
                KNIT_DIRECTIVE -> {
                    require(directive.singleLine) { "KNIT directive must end on the same line with '$DIRECTIVE_END'" }
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
                    require(directive.singleLine) { "CLEAR directive must end on the same line with '$DIRECTIVE_END'" }
                    require(directive.param.isEmpty()) { "CLEAR directive must not have parameters" }
                    code.clear()
                    continue@mainLoop
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

enum class MarkdownPart { PRE_TOC, TOC, POST_TOC }

class MarkdownTextReader(r: Reader) : LineNumberReader(r) {
    val allText = arrayListOf<String>()
    val preTocText = arrayListOf<String>()
    val postTocText = arrayListOf<String>()
    var markdownPart: MarkdownPart = MarkdownPart.PRE_TOC

    override fun readLine(): String? {
        val line = super.readLine() ?: return null
        allText += line
        when (markdownPart) {
            MarkdownPart.PRE_TOC -> preTocText += line
            MarkdownPart.POST_TOC -> postTocText += line
            MarkdownPart.TOC -> {} // do nothing
        }
        return line
    }
}

fun File.withMarkdownTextReader(block: MarkdownTextReader.() -> Unit): MarkdownTextReader {
    MarkdownTextReader(reader()).use {
        try {
            it.block()
        } catch (e: IllegalArgumentException) {
            println("ERROR: $this: ${it.lineNumber}: ${e.message}")
        }
        return it
    }
}

private fun writeLines(file: File, lines: List<String>) {
    println(" Writing $file ...")
    file.parentFile?.mkdirs()
    file.printWriter().use { out ->
        lines.forEach { out.println(it) }
    }
}
