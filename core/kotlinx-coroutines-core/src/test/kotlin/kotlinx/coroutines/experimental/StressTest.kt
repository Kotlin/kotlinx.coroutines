package kotlinx.coroutines.experimental

/**
 * Is `true` when nightly stress test is done.
 */
public actual val isStressTest = System.getProperty("stressTest") != null

public val stressTestMultiplierSqrt = if (isStressTest) 5 else 1

/**
 * Multiply various constants in stress tests by this factor, so that they run longer during nightly stress test.
 */
public actual val stressTestMultiplier = stressTestMultiplierSqrt * stressTestMultiplierSqrt
