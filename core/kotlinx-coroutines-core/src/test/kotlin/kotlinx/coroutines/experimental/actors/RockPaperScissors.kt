package kotlinx.coroutines.experimental.actors

import kotlinx.coroutines.experimental.*
import java.util.*


enum class Move {
    ROCK, PAPER, SCISSORS;

    fun wins(target: Move): Boolean {
        return (this == Move.ROCK && target == Move.SCISSORS) ||
                (this == Move.PAPER && target == Move.ROCK) ||
                (this == Move.SCISSORS && target == Move.PAPER)
    }
}

class GameCoordinator(private val rounds: Int, private val playerOne: Player, private val playerTwo: Player) : Actor() {

    private val results = mutableMapOf<Player, Int>()
    private val roundState = mutableMapOf<Player, Move>()
    private var currentRound = 1

    suspend fun start() = act {
        startRound()
    }

    private suspend fun startRound() {
        playerOne.play(this)
        playerTwo.play(this)
    }

    suspend fun receiveMove(move: Move, player: Player) = act {
        roundState[player] = move
        if (roundState.size == 2) {
            finishRound()
            roundState.clear()
        }
    }

    private suspend fun finishRound() {
        val firstMove = roundState[playerOne]!!
        val secondMove = roundState[playerTwo]!!

        val winner = when {
            firstMove.wins(secondMove) -> playerOne
            secondMove.wins(firstMove) -> playerTwo
            else -> null
        }

        if (winner != null) {
            println("${winner.name} wins round #$currentRound")
            val counter = results[winner] ?: 0
            results[winner] = counter + 1
        }  else {
            println("Draw in round #$currentRound")
        }

        if (++currentRound > rounds) {
            println("""

                Game over:
                ${playerOne.name} score: ${results[playerOne] ?: 0}
                ${playerTwo.name} score: ${results[playerTwo] ?: 0}
            """.trimIndent())
            close()
        } else {
            startRound()
        }
    }
}

class Player(val name: String) : Actor() {

    suspend fun play(coordinator: GameCoordinator) = act {
        val move = Move.values()[Random().nextInt(Move.values().size)]
        coordinator.receiveMove(move, this)
    }
}

fun main(args: Array<String>) = runBlocking {
    val game = GameCoordinator(5, Player("Player #1"), Player("Player #2"))
    game.start()
    game.join()
}
