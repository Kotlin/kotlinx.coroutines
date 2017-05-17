# Knit

This is a very simple tool that produces Kotlin source example files from a markdown document that includes
snippets of Kotlin code in its body. It is used to produce examples for 
[coroutines guide](../coroutines-guide.md) and other markdown documents.
It also includes likes to the documentation web site into the documents.

## Usage

* In project root directory do:
  * Run `mvn clean`
  * Run `mvn compile`
  * Run `mvn site` (or `mvn site -DskipJekyll` if you have don't Jekyll installed or don't want to rebuild web site)
* Commit updated documents and examples
