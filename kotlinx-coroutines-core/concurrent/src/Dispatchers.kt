/*
 * Copyright 2016-2023 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

/**
 * The [CoroutineDispatcher] that is designed for offloading blocking IO tasks to a shared pool of threads.
 * Additional threads in this pool are created on demand.
 * Default IO pool size is `64`; on JVM it can be configured using JVM-specific mechanisms,
 * please refer to `Dispatchers.IO` documentation on JVM platform.
 *
 * ### Elasticity for limited parallelism
 *
 * `Dispatchers.IO` has a unique property of elasticity: its views
 * obtained with [CoroutineDispatcher.limitedParallelism] are
 * not restricted by the `Dispatchers.IO` parallelism. Conceptually, there is
 * a dispatcher backed by an unlimited pool of threads, and both `Dispatchers.IO`
 * and views of `Dispatchers.IO` are actually views of that dispatcher. In practice
 * this means that, despite not abiding by `Dispatchers.IO`'s parallelism
 * restrictions, its views share threads and resources with it.
 *
 * In the following example
 * ```
 * // 100 threads for MySQL connection
 * val myMysqlDbDispatcher = Dispatchers.IO.limitedParallelism(100)
 * // 60 threads for MongoDB connection
 * val myMongoDbDispatcher = Dispatchers.IO.limitedParallelism(60)
 * ```
 * the system may have up to `64 + 100 + 60` threads dedicated to blocking tasks during peak loads,
 * but during its steady state there is only a small number of threads shared
 * among `Dispatchers.IO`, `myMysqlDbDispatcher` and `myMongoDbDispatcher`
 */
@Suppress("EXTENSION_SHADOWED_BY_MEMBER")
public expect val Dispatchers.IO: CoroutineDispatcher


