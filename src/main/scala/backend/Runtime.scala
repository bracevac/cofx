package elm.runtime

import javafx.embed.swing.JFXPanel

import felm.domain.Actors.Dispatcher

import scalafx.application.Platform
import scalafx.Includes._
import scalafx.scene.Scene
import scalafx.scene.control.TextArea
import scalafx.scene.input.{KeyEvent, MouseEvent}
import scalafx.stage.{Stage, WindowEvent}

object ElmRuntime {
  class MainWindow {
    val stage = new Stage {
      onCloseRequest = (ev: WindowEvent) => {
        println("Bye")
        System.exit(0) //FIXME: this doesn't work...
      }
      val pane = new TextArea {
        onKeyReleased = (event: KeyEvent) => {
          Dispatcher.notify(Dispatcher.KEY, None)
        }
        onKeyPressed = (event: KeyEvent) => {
          Dispatcher.notify(Dispatcher.KEY, Some(event.code.ordinal()))
        }
        onMouseMoved = (event: MouseEvent) => {
          Dispatcher.notify(Dispatcher.MOUSE, (event.sceneX.toInt, event.sceneY.toInt))
        }
        resizable = true
      }
      title.value = "ELM"
      width = 600
      height = 450
      resizable = true
      scene = new Scene {
        resizable = true
        root = pane
      }
    }
  }

  def run(thunk: => Unit): Unit = {
    new JFXPanel()
    Platform.runLater {
      val window = new MainWindow
      window.stage.showAndWait()
    }
    thunk
    println("ELM started")
  }
}

object ElmTest {
  import felm.Language._
  // Note: delayedInit has been deprecated

  def main(args: Array[String]): Unit = {
    ElmRuntime.run {
      mouse.foldp(0) {
        case (i,(j,k)) => i+j+k
      } += (println(_))
    }
  }
}
