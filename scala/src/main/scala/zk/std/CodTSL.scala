package zk.std

/*
 * Stackless version of the Codensity Monad Transformer used for undelimited backtracking.
 */

import scalaz.{Arrow, Monad}
import scalaz.Trampoline._
import scalaz.Free.Trampoline
import zk.{MonadTransSearch, MonadSearch}

object TrampolineArrow {
  type ==>>[A,B] = Trampoline[A => Trampoline[B]]

  object TrampolineArrowInstances extends Arrow[==>>] {
    def id[A]: A ==>> A = done((a:A) => done(a))

    def compose[A, B, C](f: B ==>> C, g: A ==>> B): A ==>> C = done((a:A) => for (x <- app(g, a); y <- app(f , x)) yield y)

    def first[A, B, C](f: A ==>> B): (A, C) ==>> (B, C) = done((p:(A,C)) => for (x <- app(f, p._1)) yield (x,p._2))

    def arr[A, B](f: (A) => B): A ==>> B = done((a:A) => delay(f(a)))
  }

  def app[A,B](f : A ==>> B, a : A) : Trampoline[B] = for (rf <- f; b <- rf(a)) yield b
  def force[A,B](f : A ==>> B) : A => B = (a:A) => {
    val rf = f.run
    rf(a).run
  }
}

import TrampolineArrow._
import TrampolineArrowInstances._

/** The StackLess Codentisty Monad Transformer class */
abstract class SLCodT[M[_],A](implicit M : Monad[M]) {
  def apply[R] : (A ==>> M[R]) ==>> M[R]

  final def run : M[A] = app(apply[A], arr(((a:A) => M.point[A](a)))).run
}

object SLCodT {
  /** unit operation of the StackLess Codensity Monad */
  def apply[M[_],A](a : => A)(implicit m : Monad[M]) : SLCodT[M,A] = new SLCodT[M,A] {
    def apply[R] : (A ==>> M[R]) ==>> M[R] = done((k : A ==>> M[R]) => app(k , a))
  }
}

/** Instances satisfied by the StackLess Codensity Monad */
trait SLCodTInstances extends MonadTransSearch[SLCodT] { self =>
  final def liftM[M[_], A](ma: M[A])(implicit M: MonadSearch[M]): SLCodT[M, A] = new SLCodT[M,A] {
    def apply[R] : (A ==>> M[R]) ==>> M[R] = done((k : A ==>> M[R]) => delay(M.bind(ma)(force(k))))
  }

  trait MonadTransSearchApply[M[_]] extends MonadSearch[({type λ[α] = SLCodT[M, α]})#λ] { MT =>
    implicit val M : MonadSearch[M]

    final def point[A](a: => A): SLCodT[M,A] = SLCodT[M,A](a)(M)

    final def bind[A, B](fa: SLCodT[M,A])(f: (A) => SLCodT[M,B]): SLCodT[M,B] = new SLCodT[M,B] {
      def apply[R] : (B ==>> M[R]) ==>> M[R] = done((k : B ==>> M[R]) => app(fa[R] , done(((a:A) => app(f(a)[R] , k)))))
    }

    final def empty[A]: SLCodT[M,A] = self.liftM[M,A](M.empty[A])

    final def plus[A](ma : SLCodT[M,A], mb : => SLCodT[M,A]): SLCodT[M,A] = new SLCodT[M,A] {
      lazy val lmb = mb
      def apply[R] : (A ==>> M[R]) ==>> M[R] = done((k : A ==>> M[R]) =>
        for (mra <- app(ma[R] , k))
        yield M.plus[R]( mra , app(lmb[R], k).run ))
    }

    final def local[A](ma : SLCodT[M,A]) : SLCodT[M,A] = new SLCodT[M,A] {
      def apply[R] : (A ==>> M[R]) ==>> M[R] = done((k : A ==>> M[R]) =>
        for (mra <- app(ma[A] , arr((x:A) => M.point(x))))
        yield M.bind[A,R](M.local[A](mra))(force(k)))
    }

    final def mtry[A](ma : SLCodT[M,A], mb : => SLCodT[M,A]): SLCodT[M,A] = new SLCodT[M,A] {
      lazy val lmb = mb
      def apply[R] : (A ==>> M[R]) ==>> M[R] = done((k : A ==>> M[R]) =>
        for (mra <- app(ma[R] , k))
        yield M.mtry[R]( mra , app(lmb[R], k).run ))
    }
  }

  final implicit def apply[M[_]](implicit pM: MonadSearch[M]): MonadSearch[({type λ[α] = SLCodT[M, α]})#λ] =
    new MonadTransSearchApply[M] { val M = pM }
}
