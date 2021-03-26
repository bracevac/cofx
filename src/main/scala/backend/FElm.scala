package felm

import scala.language.implicitConversions

import felm.domain.Actors.{Reactive, Factory, Dispatcher}

package spec {
  trait Syntax[R[_]] {
    type Sugar[T]
  }

  trait SyntaxExt[R[_]] extends Syntax[R] {
    type Sugar[T] = SugarExt[R, T]
  }

  trait SugarExt[R[_], T] {
    def lift1[U](f: T => U): R[U]
    def lift2[U, V](u: R[U])(f: (T, U) => V): R[V]
    def foldp[U](u: U)(f: (U, T) => U): R[U]
    def async: R[T]
    def +=(f: T => Unit): Unit

    def map[U](f: T => U): R[U] = lift1(f)
    def zip[U](u: R[U]): R[(T, U)] = lift2(u)((_, _))
  }

  trait FElmPredef[R[_]] {
    implicit def lift0[A](v: A): R[A]
    def timer(hz: Int): R[Int]
    def mouse: R[(Int, Int)]
    def key: R[Option[Char]]
  }

  trait FElmLang[R[_], S <: Syntax[R]] extends Syntax[R] {
    self: FElmPredef[R] =>
    val syntax: S
    implicit def enrich[T](r: R[T]): syntax.Sugar[T]
  }

  trait FElmExt[R[_]] extends FElmLang[R, SyntaxExt[R]] {
    self: FElmPredef[R] =>
  }
}

import spec._

object Language extends FElmExt[Reactive] with FElmPredef[Reactive] {
  val syntax = new SyntaxExt[Reactive] {}
  implicit def enrich[T](t: Reactive[T]): syntax.Sugar[T] = 
    new SugarExt[Reactive, T] {
      def lift1[U](f: T => U) = Factory.mkLift1(t, f)
      def lift2[U, V](u: Reactive[U])(f: (T, U) => V) = Factory.mkLift2(t, u)(f)
      def foldp[U](u: U)(f: (U, T) => U) = Factory.mkFoldp(t)(u)(f)
      def async = Factory.mkAsync(t)
      def +=(f: T => Unit) = Factory.attach(t, f)
    }
  implicit def lift0[A](v: A): Reactive[A] = Factory.mkLift0(v)
  def timer(hz: Int): Reactive[Int] = ???
  def mouse: Reactive[(Int, Int)] = Factory.mouse
  def key: Reactive[Option[Char]] = Factory.key
}
