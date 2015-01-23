package zk.std

import scalaz.{Zipper => _, Ordering => _, _}
import zk._
import Implicits._


/** Instances of the List Functor */
trait ListInstances extends MonadSearch[List] with Esrevart[List] with Unzip[List] with IsEmpty[List] with Cobind[List] {

  object scalazStd extends scalaz.std.ListInstances

  import scalazStd._

  override def ap[A, B](l: => List[A])(f: => List[A => B]): List[B] = super[MonadSearch].ap[A, B](l)(f)

  def empty[A]: List[A] = Nil

  def plus[A](a: List[A], b: => List[A]): List[A] = listInstance.plus[A](a, b)

  def isEmpty[A](fa: List[A]): Boolean = listInstance.isEmpty[A](fa)

  def traverseImpl[G[_], A, B](l: List[A])(f: A => G[B])(implicit G: Applicative[G]): G[List[B]] =
    listInstance.traverseImpl[G, A, B](l)(f)(G)

  def point[A](a: => A): List[A] = listInstance.point[A](a)

  def bind[A, B](fa: List[A])(f: (A) => List[B]): List[B] = listInstance.bind[A, B](fa)(f)

  def cobind[A, B](fa: List[A])(f: (List[A]) => B): List[B] = List(f(fa))

  def zip[A, B](a: => List[A], b: => List[B]): List[(A, B)] = listInstance.zip[A, B](a, b)

  def unzip[A, B](a: List[(A, B)]): (List[A], List[B]) = listInstance.unzip[A, B](a)

  def local[A](fa: List[A]): List[A] = fa

  def mtry[A](fa: List[A], fb: => List[A]): List[A] = if (fa.isEmpty) fb else fa

  override def mif[A, B](cond: List[A], mt: => List[B], me: => List[B]): List[B] = cond match {
    case Nil => me
    case l => mt
  }

  override def esrevart[M[_],X,Y,B](default: X => M[Y])(implicit M : MonadSearch[M]) : List[Rotareti[M,X,Y,B]] => M[Rotareti[M,List[X],List[Y],List[B]]] = {
    type R  = Rotareti[M,     X,      Y,      B ]
    type RL = Rotareti[M,List[X],List[Y],List[B]]

    def aux(l : List[R]) : M[RL] =
       if (l.forall(_.isAnswer)) M.point(Answer[M,List[X],List[Y],List[B]](l.map((r : R) => r match {
         case Answer(b) => b
         case _         => throw new Exception
       })))
       else {
         def rec(l2 : List[R]) : (List[X] , List[Y] => M[List[R]]) = l2 match {
           case Nil => (Nil, (ly: List[Y]) => M.point(Nil))
           case r :: q => {
             val (lx, fly): (List[X], List[Y] => M[List[R]]) = rec(q)
             r match {
               case a@Answer(_) => (lx, (ly: List[Y]) => M.apply(fly(ly))(a :: _))
               case Focus(x, f) => (x :: lx, (ly: List[Y]) => ly match {
                 case Nil => M.empty[List[R]]
                 case y :: t => M.bind(f(y))((rr: R) => M.apply(fly(t))((lr: List[R]) => rr :: lr))
               })
             }
           }
         }

         val (lx, fly): (List[X], List[Y] => M[List[R]]) = rec(l)
         M.point(Focus[M,List[X],List[Y],List[B]](lx , (ly : List[Y]) => M.bind(fly(ly))(aux _)))
      }

    aux _
  }
}

trait ListInstances1[A] extends Visitable[List[A], A, A, List[A], Int] {
  implicit val KeysOrdering: Ordering[Int] = Ordering.Int

  def update(pos: Int, l: List[A], asso: List[(Int, A)]): List[A] = asso match {
    case Nil => l
    case (i, e) :: q => if (pos > i) update(pos, l, q)
    else l match {
      case Nil => Nil
      case x :: r => if (pos == i) e :: update(pos + 1, r, q) else x :: update(pos + 1, r, asso)
    }
  }

  def keys(l : List[A]) : Stream[Int] = (0 to (l.length - 1)).toStream

  def default[F[_]](implicit F: Traverse[F]) : Strategy[F[A], F[A]] = Strategy.id[F[A]]

  def lens[F[_],M[_]](implicit F: Traverse[F], M: MonadSearch[M]) : F[Int] => List[A] => M[Rotareti[M, F[A],F[A],List[A]]] =
    (fk:F[Int]) => (l:List[A]) => {
      val n = l.length
      val mfc: M[F[A]] = F.traverse[M, Int, A](fk)((k: Int) => if (k < n) M.pure[A](l(k)) else M.empty[A])(M)

      M.apply(mfc)((fc: F[A]) => Focus[M, F[A], F[A], List[A]](fc , (fe: F[A]) => {
          val assocs: List[(Int, A)] = listInstances.zip(F.toList[Int](fk), F.toList[A](fe)).sortBy[Int](_._1)
          M.point(Answer[M,F[A],F[A],List[A]](update(0, l, assocs)))
        }))
    }

}
