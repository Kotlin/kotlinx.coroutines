package kotlinx.coroutines.experimental.slf4j

import mu.KotlinLogging
import org.slf4j.MDC

fun main(args: Array<String>) {
    val logger = KotlinLogging.logger {}

    // You can put values in the MDC at any time. Before anything else
    // we put the first name
    MDC.put("first", "Dorothy")

    // We now put the last name
    MDC.put("last", "Parker")

    // The most beautiful two words in the English language according
    // to Dorothy Parker:
    logger.info("Check enclosed.")
    logger.debug("The most beautiful two words in English.")

    MDC.put("first", "Richard")
    MDC.put("last", "Nixon")
    logger.info("I am not a crook.")
    logger.info("Attributed to the former US president. 17 Nov 1973.")
}
