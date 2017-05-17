# Knit

This is a very simple tool that produces Kotlin source example files from a markdown document that includes
snippets of Kotlin code in its body. It is used to produce examples for 
[coroutines guide](../coroutines-guide.md) and other markdown documents.
It also includes likes to the documentation web site into the documents.

## Usage

* In project root directory do:
  * Run `mvn clean compile site`
  * Add `-DskipJekyll` if you have don't Jekyll installed or don't want to actually rebuild documentation web 
    site static pages
* Commit updated documents and examples
