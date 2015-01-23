package zk.std

import zk._
import scalaz.{Applicative, Traverse}
import scala.collection.immutable.TreeMap
import scala.Some

//import zk.{Visitable}

trait TreeMapInstances[K] extends Traverse[({type λ[α] = TreeMap[K,α]})#λ] {
  implicit val KeysOrdering : Ordering[K]

  def traverseImpl[F[_],A,B](fa : TreeMap[K,A])(f : A => F[B])(implicit F:Applicative[F]) : F[TreeMap[K,B]] = {
    val empty : F[TreeMap[K,B]] = F.pure[TreeMap[K,B]](TreeMap.empty[K,B])
    val op    : (F[TreeMap[K,B]] , (K,A)) => F[TreeMap[K,B]] = (ftm : F[TreeMap[K,B]], p : (K,A)) => {
      val ff : (TreeMap[K,B], B) => TreeMap[K,B] = (tm : TreeMap[K,B], b : B) => tm + ((p._1,b))
      F.apply2[TreeMap[K,B], B, TreeMap[K,B]](ftm, f(p._2))(ff)
    }
    fa.foldLeft[F[TreeMap[K,B]]](empty)(op)
  }
}

trait TreeMapInstances1[K,A] extends Visitable[TreeMap[K,A], (K,A), (K,A), TreeMap[K,A], K] {
  implicit val KeysOrdering : Ordering[K]

  def keys(t : TreeMap[K,A]) = t.keys.toStream

  def default[F[_]](implicit F: Traverse[F]) : Strategy[F[(K,A)], F[(K,A)]] = Strategy.id[F[(K,A)]]

  def lens[F[_],M[_]](implicit F: Traverse[F], M: MonadSearch[M]) : F[K] => TreeMap[K,A] => M[Rotareti[M, F[(K,A)],F[(K,A)],TreeMap[K,A]]] =
    (fk:F[K]) => (t:TreeMap[K,A]) => {

    val assocs : M[F[(K,A)]] = F.traverse[M,K,(K,A)](fk)((k : K) => t.get(k) match {
      case None    => M.empty[(K,A)]
      case Some(i) => M.point[(K,A)]((k,i))
    })(M)

    val keysRemoved : TreeMap[K,A] = F.foldLeft[K,TreeMap[K,A]](fk, t)((e : TreeMap[K,A], k : K) => e - k)

    M.apply(assocs)((ea : F[(K,A)]) => Focus[M,F[(K,A)],F[(K,A)],TreeMap[K,A]]( ea , (fc : F[(K,A)]) =>
      M.point(Answer[M,F[(K,A)],F[(K,A)],TreeMap[K,A]](F.foldLeft[(K,A),TreeMap[K,A]](fc, keysRemoved)((e : TreeMap[K,A], ea2 : (K,A)) => e + ((ea2._1, ea2._2)))))
    ))
  }
}

object TreeMapFunctions {

  def traverseTreeMap[F[_],K,V,C](f :(K,V) => F[C])(implicit F:Applicative[F], K : Ordering[K]) : TreeMap[K,V] => F[TreeMap[K,C]] = {
    def aux(tm : TreeMap[K,V]) : F[TreeMap[K,C]] =
      if (tm.isEmpty) F.pure(TreeMap.empty[K,C])
      else {
        val (k,v) = tm.head
        F.apply2[C,TreeMap[K,C],TreeMap[K,C]](f(k,v), aux(tm.tail))((c : C, t : TreeMap[K,C]) => t + ((k,c)))
      }
    aux _
  }
}
