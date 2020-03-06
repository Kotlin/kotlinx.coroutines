package examples

import javafx.application.Application
import javafx.scene.Scene
import javafx.scene.control.*
import javafx.scene.layout.GridPane
import javafx.stage.Stage
import javafx.beans.property.SimpleStringProperty
import javafx.event.EventHandler
import kotlinx.coroutines.*
import kotlinx.coroutines.flow.*
import kotlinx.coroutines.javafx.*
import kotlin.coroutines.CoroutineContext

fun main(args: Array<String>) {
    Application.launch(FxAsFlowApp::class.java, *args)
}

/**
 * Adapted from
 * https://github.com/ReactiveX/RxJavaFX/blob/a78ca7d15f7d82d201df8fafb6eba732ec17e327/src/test/java/io/reactivex/rxjavafx/RxJavaFXTest.java
 */
class FxAsFlowApp: Application(), CoroutineScope {

    private var job = Job()
    override val coroutineContext: CoroutineContext
        get() = JavaFx + job

    private val incrementButton = Button("Increment")
    private val incrementLabel = Label("")
    private val textInput = TextField()
    private val flippedTextLabel = Label()
    private val spinner = Spinner<Int>()
    private val spinnerChangesLabel = Label()

    public override fun start(  primaryStage: Stage) {
        val gridPane = GridPane()
        gridPane.apply {
            hgap = 10.0
            vgap = 10.0
            add(incrementButton, 0, 0)
            add(incrementLabel, 1, 0)
            add(textInput, 0, 1)
            add(flippedTextLabel, 1, 1)
            add(spinner, 0, 2)
            add(spinnerChangesLabel, 1, 2)
        }
        val scene = Scene(gridPane)
        primaryStage.apply {
            width = 275.0
            setScene(scene)
            show()
        }
    }

    public override fun stop() {
        super.stop()
        job.cancel()
        job = Job()
    }

    init {
        // Initializing the "Increment" button
        val stringProperty = SimpleStringProperty()
        var i = 0
        incrementButton.onAction = EventHandler {
            i += 1
            stringProperty.set(i.toString())
        }
        launch {
            stringProperty.asFlow().collect {
                if (it != null) {
                    stringProperty.set(it)
                }
            }
        }
        incrementLabel.textProperty().bind(stringProperty)
        // Initializing the reversed text field
        val stringProperty2 = SimpleStringProperty()
        launch {
            textInput.textProperty().asFlow().collect {
                if (it != null) {
                    stringProperty2.set(it.reversed())
                }
            }
        }
        flippedTextLabel.textProperty().bind(stringProperty2)
        // Initializing the spinner
        spinner.valueFactory = SpinnerValueFactory.IntegerSpinnerValueFactory(0, 100)
        spinner.isEditable = true
        val stringProperty3 = SimpleStringProperty()
        launch {
            spinner.valueProperty().asFlow().collect {
                if (it != null) {
                    stringProperty3.set("NEW: $it")
                }
            }
        }
        spinnerChangesLabel.textProperty().bind(stringProperty3)
    }
}
