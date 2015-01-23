package zk.std

import zk.Esrevart
import scalaz.Applicative

/** Instances satisfied by the Pair Functor */
trait PairInstances extends Esrevart[Pair] with scalaz.Zip[Pair] with scalaz.Unzip[Pair] {
  def point[A](a: => A): (A, A) = (a, a)

  def traverseImpl[G[_], A, B](fa: (A, A))(f: (A) => G[B])(implicit G: Applicative[G]): G[(B, B)] =
    G.apply2[B, B, Pair[B]](f(fa._1), f(fa._2))((b1: B, b2: B) => (b1, b2))

  def zip[A, B](a: => (A, A), b: => (B, B)): ((A, B), (A, B)) = ((a._1, b._1), (a._2, b._2))

  def unzip[A, B](a: ((A, B), (A, B))): ((A, A), (B, B)) = {
    val l = a._1
    val r = a._2
    ((l._1, r._1), (l._2, r._2))
  }
}
