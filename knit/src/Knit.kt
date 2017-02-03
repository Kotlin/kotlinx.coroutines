import java.io.File
import java.io.IOException
import java.io.LineNumberReader

val KNIT_DIRECTIVE = "<!--- KNIT "
val INCLUDE_DIRECTIVE = "<!--- INCLUDE "
val CLEAR_DIRECTIVE = "<!--- CLEAR "
val DIRECTIVE_END = "-->"

val CODE_START = "```kotlin"
val CODE_END = "```"

fun main(args: Array<String>) {
    if(args.size != 1) {
        println("Usage: Knit <markdown-file>")
        return
    }
    var knitRegex: Regex? = null
    val includes = arrayListOf<Include>()
    val code = arrayListOf<String>()
    val files = mutableSetOf<String>()
    File(args[0]).withLineNumberReader {
        mainLoop@ while (true) {
            val inLine = readLine() ?: break
            when {
                inLine.startsWith(KNIT_DIRECTIVE) -> {
                    require(inLine.endsWith(DIRECTIVE_END)) { "KNIT directive must end on the same line with '$DIRECTIVE_END'" }
                    require(knitRegex == null) { "Only one KNIT directive is supported"}
                    knitRegex = Regex("\\((" + inLine.substring(KNIT_DIRECTIVE.length, inLine.length - DIRECTIVE_END.length).trim() + ")\\)")
                    continue@mainLoop
                }
                inLine.startsWith(INCLUDE_DIRECTIVE) -> {
                    val include = Include(Regex(inLine.substring(INCLUDE_DIRECTIVE.length).trim()))
                    while (true) {
                        val includeLine = readLine() ?: break
                        if (includeLine.startsWith(DIRECTIVE_END)) break
                        include.lines += includeLine
                    }
                    includes += include
                    continue@mainLoop
                }
                inLine.startsWith(CODE_START) -> {
                    code += ""
                    while (true) {
                        val codeLine = readLine() ?: break
                        if (codeLine.startsWith(CODE_END)) break
                        code += codeLine
                    }
                    continue@mainLoop
                }
                inLine.startsWith(CLEAR_DIRECTIVE) -> {
                    require(inLine.endsWith(DIRECTIVE_END)) { "CLEAR directive must end on the same line with '$DIRECTIVE_END'" }
                    code.clear()
                    continue@mainLoop
                }
            }
            knitRegex?.find(inLine)?.let { knitMatch ->
                val file = knitMatch.groups[1]!!.value
                require(files.add(file)) { "Duplicate file name: $file"}
                println("Knitting $file ...")
                val outLines = arrayListOf<String>()
                for (include in includes) {
                    val includeMatch = include.regex.matchEntire(file) ?: continue
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
                val oldLines = try { File(file).readLines() } catch (e: IOException) { emptyList<String>() }
                if (outLines != oldLines) {
                    println(" Writing $file ...")
                    File(file).printWriter().use { out ->
                        outLines.forEach { out.println(it) }
                    }
                }
            }
        }
    }
}

class Include(val regex: Regex, val lines: MutableList<String> = arrayListOf())

fun File.withLineNumberReader(block: LineNumberReader.() -> Unit) {
    LineNumberReader(reader()).use {
        try {
            it.block()
        } catch (e: IllegalArgumentException) {
            println("ERROR: $this: ${it.lineNumber}: ${e.message}")
        }
    }
}
