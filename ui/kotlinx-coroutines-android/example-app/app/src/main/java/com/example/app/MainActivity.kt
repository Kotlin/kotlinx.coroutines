package com.example.app

import android.os.Bundle
import android.support.v7.app.AppCompatActivity
import android.view.Menu
import android.view.MenuItem
import android.view.View
import android.widget.Toast
import kotlinx.android.synthetic.main.activity_main.*
import kotlinx.android.synthetic.main.content_main.*
import kotlinx.coroutines.*

class MainActivity : AppCompatActivity() {

    var job: Job? = null

    override fun onCreate(savedInstanceState: Bundle?) {
        super.onCreate(savedInstanceState)
        setContentView(R.layout.activity_main)
        setSupportActionBar(toolbar)

        buttonEmptyTask.setOnClickListener { startEmptyTask() }
        buttonTaskWithProgress.setOnClickListener { startTaskWithProgress() }
        buttonCancelableTask.setOnClickListener { startCancelableTask() }
        buttonCancelTask.setOnClickListener { cancelTask() }
    }

    override fun onCreateOptionsMenu(menu: Menu): Boolean {
        // Inflate the menu; this adds items to the action bar if it is present.
        menuInflater.inflate(R.menu.menu_main, menu)
        return true
    }

    override fun onOptionsItemSelected(item: MenuItem): Boolean {
        // Handle action bar item clicks here. The action bar will
        // automatically handle clicks on the Home/Up button, so long
        // as you specify a parent activity in AndroidManifest.xml.
        val id = item.itemId
        if (id == R.id.action_settings) return true
        return super.onOptionsItemSelected(item)
    }

    private fun startEmptyTask() {
        println("start empty task")
        GlobalScope.launch(Dispatchers.Main) {
            delay(1000)
            showText("Hello from Kotlin Coroutines!")
        }
    }

    private fun startTaskWithProgress() {
        println("start Empty With Progress")
        GlobalScope.launch(Dispatchers.Main) {
            progressBar.visibility = View.VISIBLE
            delay(5000)
            showText("Hello from Kotlin Coroutines!")
            progressBar.visibility = View.GONE
        }
    }

    @UseExperimental(InternalCoroutinesApi::class)
    private fun startCancelableTask() {
        println("start cancelable Task")
        job = GlobalScope.launch(Dispatchers.Main) {
            progressBar.visibility = View.VISIBLE
            delay(5000)
            showText("Hello from Kotlin Coroutines!")
            progressBar.visibility = View.GONE
        }
        job?.invokeOnCompletion(true) {
            if (it != null) {
                job?.cancel()
                showText("Cancelable Task was cancel")
                progressBar.visibility = View.GONE
            }
        }
    }

    private fun showText(text: String) {
        Toast.makeText(this, text, Toast.LENGTH_SHORT).show()
    }

    private fun cancelTask() {
        job?.cancel()
    }
}