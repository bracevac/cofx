package felm.domain

import akka.actor.{Actor, ActorRef, ActorSystem, Cancellable, Props}
import scala.concurrent.duration.{Duration, FiniteDuration}
import scala.language.implicitConversions

object Actors {
  type Channel[T] = ActorRef
  case class Reactive[T](out: Channel[T])

  object Dispatcher {
    type Id = Long
    //val TIMER: Id = ???
    val MOUSE: Id = 0
    val KEY: Id = 1

    def notify(id: Id, v: Any): Unit = actor ! NewEvent(id, v)

    sealed trait DispatcherMessage[T]
    case class NewEvent[T](id: Id, value: T) extends DispatcherMessage[T]
    case class NewListener[T](asyncActor: ActorRef, listenerActor: ActorRef) extends DispatcherMessage[T]

    class DispatcherActor(predef: Map[Long, ActorRef]) extends Actor {
      var _id: Long = predef.keys.max
      def nextId: Long = {
        val res = _id
        _id = _id + 1
        res
      }
      //propagation round #no
      var round: Long = 0L
      var listeners: Map[Id, ActorRef] = predef

      def receive = {
        case NewEvent(id, v) if listeners.contains(id) =>
          for ((i, lsn) <- listeners)
            lsn ! EventListenerActor.NewEvent(round, id, v)
            round += 1

        case NewListener(async, listener) =>
          val id = nextId
          listeners = listeners + (id -> listener)
          listener ! EventListenerActor.Enabled(id, async)
      }
    }

    lazy val (mouse, mouseAct) = Factory.mkPredefinedListener[(Int, Int)](MOUSE, Some(0,0))
    lazy val (key, keyAct) = Factory.mkPredefinedListener[Option[Char]](KEY, Some(None))
    lazy val predefined: Map[Id, ActorRef] = Map(MOUSE -> mouseAct, KEY -> keyAct)
    lazy val actor = Factory.system.actorOf(Props(new DispatcherActor(predefined)))
  }

  object Factory {
    lazy val system = ActorSystem("FElm")
    def mkChannel[T]: Channel[T] = system.actorOf(Props(new ChannelActor[T]()))

    lazy val mouse = Dispatcher.mouse
    lazy val key = Dispatcher.key

    def attach[T](r: Reactive[T], f: T => Unit): Unit = r.out ! ChannelActor.Callback(f)

    def mkLift0[A](v: A): Reactive[A] = {
      val out = mkChannel[A]
      val actor = system.actorOf(Props(new Lift0Actor(v, out)))
      Dispatcher.actor ! Dispatcher.NewListener(null, actor) //TODO better have distinct message type
      Reactive(out)
    }

    def mkLift1[T, U](r: Reactive[T], f: T => U): Reactive[U] = {
      val out = mkChannel[U]
      val actor = system.actorOf(Props(new Lift1Actor(f, out)))
      r.out ! ChannelActor.Register(actor)
      Reactive(out)
    }

    def mkLift2[T, U, V](r: Reactive[T], s: Reactive[U])(f: (T, U) => V): Reactive[V] = {
      val out = mkChannel[V]
      val actor = system.actorOf(Props(new Lift2Actor(r.out, s.out, f, out)))
      r.out ! ChannelActor.Register(actor)
      s.out ! ChannelActor.Register(actor)
      Reactive(out)
    }

    def mkFoldp[T, U](r: Reactive[T])(v: U)(f: (U, T) => U): Reactive[U] = {
      val out = mkChannel[U]
      val actor = system.actorOf(Props(new FoldActor[U, T](v, f, out)))
      r.out ! ChannelActor.Register(actor)
      Reactive(out)
    }

    def mkAsync[T](r: Reactive[T]): Reactive[T] = {
      val out = mkChannel[T]
      val asyncActor = system.actorOf(Props(new AsyncActor[T](r.out)))
      val listenerActor = system.actorOf(Props(new EventListenerActor(out)))
      Dispatcher.actor ! Dispatcher.NewListener(asyncActor, listenerActor)
      Reactive(out)
    }

    def mkTimer(period: FiniteDuration): Reactive[Timestamp] = {
      val out = mkChannel[Timestamp]
      ???
      // system.scheduler.schedule()
    }

    def mkPredefinedListener[T](id: Dispatcher.Id, default: Option[T]): (Reactive[T], ActorRef) = {
      val out = mkChannel[T]
      val actor = system.actorOf(Props(new EventListenerActor[T](default, out) {
        override def receive = listening(id)
      }))
      (Reactive(out), actor)
    }
  }

  class ChannelActor[T] extends Actor {
    import collection.mutable.ArrayBuffer
    val sinks: ArrayBuffer[ActorRef] = ArrayBuffer()
    val callbacks: ArrayBuffer[T => Unit] = ArrayBuffer()
    def receive = {
      case ChannelActor.Register(actor) =>
        sinks += actor
      case ChannelActor.Forward(msg) =>
        msg match {
          case Change(value, round) =>
            val v = value.asInstanceOf[T]
            for (f <- callbacks) f(v)
          case _ =>
        }
        for(s <- sinks) s ! msg
      case ChannelActor.Callback(f) =>
        callbacks += f.asInstanceOf[T => Unit]
    }
  }

  object ChannelActor {
    sealed trait ChannelMsg[T]
    case class Register[T](sink: ActorRef) extends ChannelMsg[T]
    case class Forward[T](msg: NodeMessage[T]) extends ChannelMsg[T]
    case class Callback[T](callback: T => Unit) extends ChannelMsg[T]
  }

  sealed trait NodeMessage[T] {
    val v: T
    val round: Long
  }
  case class NoChange[V](v: V, round: Long) extends NodeMessage[V]
  case class Change[V](v: V, round: Long) extends NodeMessage[V]

  class FoldActor[T,U](init: T, f: (T, U) => T, out: Channel[U]) extends Actor {
    var current: T = init
    def receive = {
      case Change(v, r) =>
        current = f(current, v.asInstanceOf[U])
        out ! ChannelActor.Forward(Change(current, r))
      case m@NoChange(v, r) =>
        out ! ChannelActor.Forward(NoChange(current, r))
    }
  }

  class Lift0Actor[T](v: T, out: Channel[T]) extends Actor {
    def awaitRegistration: Receive = {
      case EventListenerActor.Enabled(id, _) =>
        context.become(listening, discardOld = true)
    }
    def listening: Receive = {
      case EventListenerActor.NewEvent(r, _, _) =>
        out ! ChannelActor.Forward(NoChange(v, r))
    }
    def receive = awaitRegistration
  }

  class Lift1Actor[T,U](f: T => U, out: Channel[U]) extends Actor {
    def receive = {
      case Change(v, r) =>
        out ! ChannelActor.Forward(Change(f(v.asInstanceOf[T]), r))
      case NoChange(v, r) =>
        out ! ChannelActor.Forward(NoChange(f(v.asInstanceOf[T]), r))
    }
  }

  class Lift2Actor[T,U,V](in1: Channel[T], in2: Channel[U], f: (T,U) => V, out: Channel[V]) extends Actor { outer =>
    type Queue[A] = collection.mutable.Queue[NodeMessage[A]]
    val buffer1: Queue[T] = collection.mutable.Queue()
    val buffer2: Queue[U] = collection.mutable.Queue()

    //initially, we need to avoid glitches due to potentially missed out propagation rounds
    def justJoined: Receive = {
      // XXX: new lower1/lower2 every time justJoined is called?
      var lower1: Option[Long] = None
      var lower2: Option[Long] = None

      def tryAlign: Unit = {
        for (l1 <- lower1; l2 <- lower2) {
          if (l1 < l2)
            buffer1.drop((l2 - l1).toInt)
          else if (l2 < l1)
            buffer2.drop((l1 - l2).toInt)
          tryEmit
          context.become(emitting, discardOld = true)
          // XXX: what's exactly the behavior of become?
        }
      }
      {
        case m: NodeMessage[_] if sender() == in1 =>
          stash(m.asInstanceOf[NodeMessage[T]], buffer1)
          lower1 = Some(lower1.getOrElse(m.round))
          tryAlign
        case m: NodeMessage[_] if sender() == in2 =>
          stash(m.asInstanceOf[NodeMessage[U]], buffer2)
          lower2 = Some(lower2.getOrElse(m.round))
          tryAlign
      }
    }

    //our input buffers are in sync with the propagation
    def emitting: Receive = {
      case m: NodeMessage[_] if sender() == in1 =>
        stash(m.asInstanceOf[NodeMessage[T]], buffer1)
        tryEmit
      case m: NodeMessage[_] if sender() == in2 =>
        stash(m.asInstanceOf[NodeMessage[U]], buffer2)
        tryEmit
    }

    def receive = justJoined

    def tryEmit: Unit = {
      val joined = buffer1 zip buffer2
      for ((m1, m2) <- joined) {
        require(m1.round == m2.round, s"Round mismatch in join, this is a bug!")
        val round = m1.round
        (m1, m2) match {
          case (NoChange(_, _), NoChange(_, _)) =>
            out ! ChannelActor.Forward(NoChange(f(m1.v, m2.v), round))
          case (_, _) =>
            out ! ChannelActor.Forward(Change(f(m1.v, m2.v), round))
        }
      }
      buffer1.drop(joined.length)
      buffer2.drop(joined.length)
    }

    def stash[A](m: NodeMessage[A], buffer: Queue[A]): Unit = {
      buffer += m
    }
  }

  class AsyncActor[T](in: Channel[T]) extends Actor {
    def awaitRegistration: Receive = {
      case AsyncActor.Enabled(id) =>
        in ! ChannelActor.Register(self)
        context.become(emitting(id), discardOld = true)
    }

    def emitting(id: Dispatcher.Id): Receive = {
      case NoChange(_,_) =>
      case Change(v,_) =>
        Dispatcher.actor ! Dispatcher.NewEvent(id, v)
    }

    def receive = awaitRegistration
  }

  object AsyncActor {
    case class Enabled(id: Dispatcher.Id)
  }

  class EventListenerActor[T](default: Option[T], out: Channel[T]) extends Actor {
    def this(out: Channel[T]) = this(None, out)

    var current: Option[T] = default
    def awaitRegistration: Receive = {
      case EventListenerActor.Enabled(id, async) if sender() == Dispatcher.actor =>
        async ! AsyncActor.Enabled(id)
        val next = if (current.isDefined) listening(id) else awaitFirstValue(id)
        context.become(next, discardOld = true)
    }

    def awaitFirstValue(id: Dispatcher.Id): Receive = {
      case EventListenerActor.NewEvent(r, i, v) if sender() == Dispatcher.actor =>
        if (id == i) {
          current = Some(v.asInstanceOf[T])
          out ! ChannelActor.Forward(Change(current.get, r))
          context.become(listening(id), discardOld = true)
        }
    }

    def updateCurrent(v: T) = {
      current = Some(v)
    }

    def listening(id: Dispatcher.Id): Receive = {
      case EventListenerActor.NewEvent(r, i, v) if sender() == Dispatcher.actor =>
        if (id == i) {
          updateCurrent(v.asInstanceOf[T])
          out ! ChannelActor.Forward(Change(current.get, r))
        }
        else out ! ChannelActor.Forward(NoChange(current.get, r))
    }

    def receive = awaitRegistration
  }

  object EventListenerActor {
    case class NewEvent[T](round: Long, id: Dispatcher.Id, value: T)
    case class Enabled(id: Dispatcher.Id, asyncActor: ActorRef)
  }

  type Timestamp = Long

  class TimerListener(period: FiniteDuration, out: Channel[Timestamp]) 
    extends EventListenerActor[Timestamp](Some(System.nanoTime()), out) {
    override def awaitRegistration: Receive = {
      case EventListenerActor.Enabled(id, _) if sender() == Dispatcher.actor =>
        context.become(listening(id), discardOld = true)
    }

    override def updateCurrent(v: Timestamp) = {
      //TODO sporadically check for clock drift
      current.map(_+period.toNanos)
    }
  }

  class TimerCancel(val underlying: Cancellable, timerListener: ActorRef) extends Cancellable {
    def cancel() = {
      //timerListener ! TimerListener.Terminate
      underlying.cancel()
    }

    def isCancelled = underlying.isCancelled
  }
}
