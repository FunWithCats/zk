package zk.std

import scalaz._
import zk._
import zk.syntax._

import scalaz.Id._

/** Instances of the Identity Monad Transformer */
trait IdInstances extends Traverse[Id] with Monad[Id] with Comonad[Id] with Distributive[Id]
with scalaz.Zip[Id] with Unzip[Id] with Cozip[Id] with Esrevart[Id] with MonadSearchInjection[Id] {

  def point[A](a: => A): Id[A] = a

  def bind[A, B](fa: Id[A])(f: (A) => Id[B]): Id[B] = f(fa)

  def cobind[A, B](fa: Id[A])(f: (Id[A]) => B): Id[B] = f(fa)

  override def ap[A, B](fa: => A)(f: => A => B): B = f(fa)

  def zip[A, B](a: => Id[A], b: => Id[B]): Id[(A, B)] = (a, b)

  def unzip[A, B](a: Id[(A, B)]): (Id[A], Id[B]) = a

  def traverseImpl[G[_], A, B](l: Id[A])(f: A => G[B])(implicit G: Applicative[G]): G[Id[B]] = f(l)

  def distributeImpl[G[_], A, B](fa: G[A])(f: (A) => Id[B])(implicit G: Functor[G]): Id[G[B]] = G.map(fa)(f)

  def copoint[A](p: Id[A]): A = p

  def cozip[A, B](x: Id[\/[A, B]]): \/[Id[A], Id[B]] = x

  override def cojoin[A](fa: A): A = fa

  override def esrevart[M[_],X,Y,B](default: X => M[Y])(implicit M : MonadSearch[M]) : Id[Rotareti[M,X,Y,B]] => M[Rotareti[M,Id[X],Id[Y],Id[B]]] =
    (x:Rotareti[M,X,Y,B]) => M.point(x)

  override def liftELens[M[_],A,X,Y,B](f: ELens[M,A,X,Y,B])(implicit M : MonadSearch[M]) : ELens[M,Id[A],Id[X],Id[Y],Id[B]] = f

  def monadSearchInject[M[_]](implicit M : MonadSearch[M]) : NaturalTransformation[Id,M] = new NaturalTransformation[Id,M] {
    def apply[A](fa: Id[A]): M[A] = M.point[A](fa)
  }
}

