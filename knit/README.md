# Knit

This is a very simple tool that produces Kotlin source example files from a markdown document that includes
snippets of Kotlin code in its body. It is used to produce examples for 
[coroutines guide](../coroutines-guide.md).

## Updating guide

* In project root directory do:
  * Run `mvn clean`
  * Run `mvn compile`
  * Run `mvn pre-site` (or `mvn site` if you have Jekyll)
  * Run `Knit coroutines-guide.md` (from IDEA, mark `knit/src` as source root first)
* Commit updated `coroutines-guide.md` and examples

