package inmemorychat

open class Message

/**
 * A command that means that a user should send a message to one of user's friends
 */
class SendMessage : Message()

/**
 * A message from one of the users to another one
 */
class UserMessage(private val userId : Long, val seconds : Long, val nanos : Int) : Message()