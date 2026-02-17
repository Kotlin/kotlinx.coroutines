package kotlinx.coroutines.flow.terminal

import kotlinx.coroutines.flow.*
import kotlinx.coroutines.testing.*
import kotlin.test.*

class ToMapCollectionSamplesTest : TestBase() {
    @Test
    fun testAssociate() = runTest {
        val names = flowOf("Grace Hopper", "Jacob Bernoulli", "Johann Bernoulli")
        val byLastName = names.associate { it.split(" ").let { (firstName, lastName) -> lastName to firstName } }
        assertEquals(listOf("Hopper" to "Grace", "Bernoulli" to "Johann"), byLastName.toList())
    }

    @Test
    fun testAssociateBy() = runTest {
        data class Person(val firstName: String, val lastName: String) {
            override fun toString(): String = "$firstName $lastName"
        }
        val scientists = flowOf(Person("Grace", "Hopper"), Person("Jacob", "Bernoulli"), Person("Johann", "Bernoulli"))
        val byLastName = scientists.associateBy { it.lastName }
        assertEquals(
            listOf("Hopper" to Person("Grace", "Hopper"), "Bernoulli" to Person("Johann", "Bernoulli")),
            byLastName.toList()
        )
    }

    @Test
    fun testAssociateByWithValueTransform() = runTest {
        data class Person(val firstName: String, val lastName: String)
        val scientists = flowOf(Person("Grace", "Hopper"), Person("Jacob", "Bernoulli"), Person("Johann", "Bernoulli"))
        val byLastName = scientists.associateBy({ it.lastName }, { it.firstName })
        assertEquals(listOf("Hopper" to "Grace", "Bernoulli" to "Johann"), byLastName.toList())
    }

    @Test
    fun testAssociateByTo() = runTest {
        data class Person(val firstName: String, val lastName: String) {
            override fun toString(): String = "$firstName $lastName"
        }
        val scientists = flowOf(Person("Grace", "Hopper"), Person("Jacob", "Bernoulli"), Person("Johann", "Bernoulli"))
        val byLastName = mutableMapOf<String, Person>()
        assertTrue(byLastName.isEmpty())
        scientists.associateByTo(byLastName) { it.lastName }
        assertTrue(byLastName.isNotEmpty())
        assertEquals(
            listOf("Hopper" to Person("Grace", "Hopper"), "Bernoulli" to Person("Johann", "Bernoulli")),
            byLastName.toList()
        )
    }

    @Test
    fun testAssociateByToWithValueTransform() = runTest {
        data class Person(val firstName: String, val lastName: String)
        val scientists = flowOf(Person("Grace", "Hopper"), Person("Jacob", "Bernoulli"), Person("Johann", "Bernoulli"))
        val byLastName = mutableMapOf<String, String>()
        assertTrue(byLastName.isEmpty())
        scientists.associateByTo(byLastName, { it.lastName }, { it.firstName })
        assertTrue(byLastName.isNotEmpty())
        assertEquals(listOf("Hopper" to "Grace", "Bernoulli" to "Johann"), byLastName.toList())
    }

    @Test
    fun testAssociateTo() = runTest {
        data class Person(val firstName: String, val lastName: String)
        val scientists = flowOf(Person("Grace", "Hopper"), Person("Jacob", "Bernoulli"), Person("Johann", "Bernoulli"))
        val byLastName = mutableMapOf<String, String>()
        assertTrue(byLastName.isEmpty())
        scientists.associateTo(byLastName) { it.lastName to it.firstName }
        assertTrue(byLastName.isNotEmpty())
        assertEquals(listOf("Hopper" to "Grace", "Bernoulli" to "Johann"), byLastName.toList())
    }

    @Test
    fun testAssociateWith() = runTest {
        val words = flowOf("a", "abc", "ab", "def", "abcd")
        val withLength = words.associateWith { it.length }
        assertEquals(listOf("a", "abc", "ab", "def", "abcd"), withLength.keys.toList())
        assertEquals(listOf(1, 3, 2, 3, 4), withLength.values.toList())
    }

    @Test
    fun associateWithTo() = runTest {
        data class Person(val firstName: String, val lastName: String) {
            override fun toString(): String = "$firstName $lastName"
        }
        val scientists = flowOf(Person("Grace", "Hopper"), Person("Jacob", "Bernoulli"), Person("Jacob", "Bernoulli"))
        val withLengthOfNames = mutableMapOf<Person, Int>()
        assertTrue(withLengthOfNames.isEmpty())
        scientists.associateWithTo(withLengthOfNames) { it.firstName.length + it.lastName.length }
        assertTrue(withLengthOfNames.isNotEmpty())
        assertEquals(
            listOf(Person("Grace", "Hopper") to 11, Person("Jacob", "Bernoulli") to 14),
            withLengthOfNames.toList()
        )
    }

    @Test
    fun testGroupBy() = runTest {
        val words = flowOf("a", "abc", "ab", "def", "abcd")
        val byLength = words.groupBy { it.length }
        assertEquals(listOf(1, 3, 2, 4), byLength.keys.toList())
        assertEquals(listOf(listOf("a"), listOf("abc", "def"), listOf("ab"), listOf("abcd")), byLength.values.toList())
        val mutableByLength: MutableMap<Int, MutableList<String>> = words.groupByTo(mutableMapOf()) { it.length }
        assertEquals(mutableByLength, byLength)
    }

    @Test
    fun testGroupByWithValueTransform() = runTest {
        val nameToTeam = flowOf("Alice" to "Marketing", "Bob" to "Sales", "Carol" to "Marketing")
        val namesByTeam = nameToTeam.groupBy({ it.second }, { it.first })
        assertEquals(listOf("Marketing" to listOf("Alice", "Carol"), "Sales" to listOf("Bob")), namesByTeam.toList())
        val mutableNamesByTeam = nameToTeam.groupByTo(HashMap(), { it.second }, { it.first })
        assertEquals(namesByTeam, mutableNamesByTeam)
    }
}
