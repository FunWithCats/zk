package zk.std

import scalaz._
import zk._

/** Instances satisfied by the Option Monad */
trait OptionInstances extends MonadSearch[Option] with Cozip[Option] with Esrevart[Option]
with Unzip[Option] with IsEmpty[Option] with Cobind[Option] {

  object OptionInstances extends scalaz.std.OptionInstances

  import OptionInstances._

  override def ap[A, B](l: => Option[A])(f: => Option[A => B]): Option[B] = super[MonadSearch].ap[A, B](l)(f)

  def empty[A]: Option[A] = optionInstance.empty[A]

  def plus[A](a: Option[A], b: => Option[A]): Option[A] = optionInstance.plus[A](a, b)

  def isEmpty[A](fa: Option[A]): Boolean = optionInstance.isEmpty[A](fa)

  def traverseImpl[G[_], A, B](o: Option[A])(f: A => G[B])(implicit G: Applicative[G]): G[Option[B]] =
    optionInstance.traverseImpl[G, A, B](o)(f)(G)

  def point[A](a: => A): Option[A] = optionInstance.point[A](a)

  def bind[A, B](fa: Option[A])(f: (A) => Option[B]): Option[B] = optionInstance.bind[A, B](fa)(f)

  def cobind[A, B](fa: Option[A])(f: (Option[A]) => B): Option[B] = Some(f(fa))

  def zip[A, B](a: => Option[A], b: => Option[B]): Option[(A, B)] = optionInstance.zip[A, B](a, b)

  def unzip[A, B](a: Option[(A, B)]): (Option[A], Option[B]) = optionInstance.unzip[A, B](a)

  def cozip[A, B](x: Option[\/[A, B]]): \/[Option[A], Option[B]] = optionInstance.cozip[A, B](x)

  def local[A](fa: Option[A]): Option[A] = fa

  def mtry[A](fa: Option[A], fb: => Option[A]): Option[A] = if (fa.isEmpty) fb else fa

  override def mif[A, B](cond: Option[A], mt: => Option[B], me: => Option[B]): Option[B] = cond match {
    case None => me
    case Some(a) => mt
  }
}

/** Instances satisfied by the SlackLess Option Monad */
trait SLOptionInstances extends MonadSearch[SLOption] with Cozip[SLOption] with Esrevart[SLOption]
with Unzip[SLOption] with IsEmpty[SLOption] with Cobind[SLOption] {
  import scalaz.Trampoline._

  override def ap[A, B](l: => SLOption[A])(f: => SLOption[A => B]): SLOption[B] = super[MonadSearch].ap[A, B](l)(f)

  def empty[A]: SLOption[A] = done(None)
  def isEmpty[A](fa: SLOption[A]): Boolean = fa.run.isEmpty

  def plus[A](a: SLOption[A], b: => SLOption[A]): SLOption[A] = a.flatMap({
      case None    => b
      case Some(a) => done(Some(a))
    })


  def traverseImpl[G[_], A, B](o: SLOption[A])(f: A => G[B])(implicit G: Applicative[G]): G[SLOption[B]] = o.run match {
     case None    => G.pure(done(None))
     case Some(a) => G.apply(f(a))(x => done(Some(x)))
   }


  def point[A](a: => A): SLOption[A] = delay(Some(a))

  def bind[A, B](fa: SLOption[A])(f: (A) => SLOption[B]): SLOption[B] =
    fa.flatMap({
      case None    => done(None)
      case Some(a) => f(a)
    })

  def cobind[A, B](fa: SLOption[A])(f: (SLOption[A]) => B): SLOption[B] = delay(Some(f(fa)))

  def zip[A, B](a: => SLOption[A], b: => SLOption[B]): SLOption[(A, B)] =
    a.flatMap({
      case None     => done(None)
      case Some(va) => b.flatMap({
        case None => done(None)
        case Some(vb) => done(Some((va,vb)))
      })
    })

  def unzip[A, B](a: SLOption[(A, B)]): (SLOption[A], SLOption[B]) = {
    var oab : Option[(A,B)] = null

    val f : () => SLOption[(A,B)] = () => {
      if (oab == null) for (ab <- a) yield { oab = ab ; ab }
      else done(oab)
    }

    (for (vab <- f()) yield (for (ab <- vab) yield ab._1), for (vab <- f()) yield (for (ab <- vab) yield ab._2))
  }


  def cozip[A, B](x: SLOption[\/[A, B]]): \/[SLOption[A], SLOption[B]] =
    x.run match {
      case None => -\/(done(None))
      case Some(-\/(a)) => -\/(done(Some(a)))
      case Some(\/-(b)) => \/-(done(Some(b)))
    }

  def local[A](fa: SLOption[A]): SLOption[A] = fa

  def mtry[A](a: SLOption[A], b: => SLOption[A]): SLOption[A] =
    a.flatMap({
      case None    => b
      case Some(a) => done(Some(a))
    })

  override def mif[A, B](cond: SLOption[A], mt: => SLOption[B], me: => SLOption[B]): SLOption[B] =
    cond.flatMap({
    case None    => me
    case Some(a) => mt
  })
}
