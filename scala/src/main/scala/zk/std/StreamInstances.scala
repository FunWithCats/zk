package zk.std

import scalaz.{Applicative, Traverse}
import scala._
import zk.MonadSearch

/** Instances satisfied by the Stream Functor */
trait StreamInstances extends Traverse[Stream] with MonadSearch[Stream] with scalaz.Unzip[Stream] with scalaz.Zip[Stream] {
  def point[A](a : =>A) : Stream[A] = Stream[A](a)
  def bind[A,B](fa : Stream[A])(f : A => Stream[B]) : Stream[B] = fa.flatMap(f)

  def traverseImpl[G[_], A, B](fa: Stream[A])(f: (A) => G[B])(implicit G: Applicative[G]): G[Stream[B]] = {
    def aux(s : Stream[A]) : G[Stream[B]] =
      if (s.isEmpty) G.pure[Stream[B]](Stream.empty[B])
      else G.apply2[B,Stream[B],Stream[B]](f(s.head), aux(s.tail))((b:B, s2:Stream[B]) => s2.+:(b))

    aux(fa)
  }

  def empty[A] : Stream[A] = Stream[A]()
  def plus[A](fa : Stream[A], fb : =>Stream[A]) : Stream[A] = fa ++ fb

  def local[A](fa : Stream[A]) : Stream[A] = fa
  def mtry[A](fa : Stream[A], fb : =>Stream[A]) : Stream[A] = if (fa.isEmpty) fa else fb

  def zip[A,B](fa : =>Stream[A], fb : =>Stream[B]) : Stream[(A,B)] =
    if (fa.isEmpty || fb.isEmpty) Stream.empty[(A,B)]
    else zip(fa.tail, fb.tail).+:((fa.head,fb.head))

  def unzip[A,B](fab : Stream[(A,B)]) : (Stream[A], Stream[B]) = (map(fab)(_._1) , map(fab)(_._2))
}
