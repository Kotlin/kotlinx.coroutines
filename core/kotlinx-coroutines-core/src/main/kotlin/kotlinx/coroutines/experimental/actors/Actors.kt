package kotlinx.coroutines.experimental.actors


/**
 * Worker pool pattern support for typed actors.
 *
 * Creates [parallelism] actors by given [actorFactory] for parallel task processing
 * and wraps them in the actor of the same type, which dispatches all tasks from its mailbox to workers in round robin fashion.
 * Resulting hierarchy of actors will have the following form:
 * `parent (TypedActor<*>) <- router actor (T) <- parallelism * [worker actor (T)]`
 *
 * Close will be called on all created actors (TODO is this really that useful?).
 * It's guaranteed that [actorFactory] will be called exactly [parallelism] + 1 times.
 *
 * TODO provide example of usage
 * @param parallelism how many workers should be created for pool
 * @param parent owner of given worker (TODO allow orphan parallel workers?)
 * @param actorFactory factory to create actors for pool. Should be idempotent and all created actors should be indistinguishable
 */
//fun <T : BatchActor<T>> workerPool(parallelism: Int, parent: Actor, actorFactory: () -> T): T {
//    require(parallelism > 1) { "Expected parallelism >1, but has $parallelism" }
//    dispatcherParent.set(parent)
//    val router: T
//    try {
//        router = actorFactory()
//    } finally {
//        dispatcherParent.set(null)
//    }
//
//    dispatcher.set(router)
//    try {
//        repeat(parallelism) {
//            actorFactory()
//        }
//    } finally {
//        dispatcher.set(null)
//    }
//
//
//    return router
//    TODO()
//}

//fun <T : BatchActor<T>> workerPool(parallelism: Int, parent: Job, actorFactory: () -> T): T = TODO()