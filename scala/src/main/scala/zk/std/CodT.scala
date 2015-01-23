package zk.std

import scalaz.Monad
import zk.{MonadTransSearch, MonadSearch}

/** Codensity Monad Transformer.
  *
  * @param  M the underlying monad type.
  * @tparam M the underlying monad instance.
  * @tparam A .
  */
abstract class CodT[M[_],A](implicit M : Monad[M]) {
  def apply[R](k : A => M[R]) : M[R]
  final def run : M[A] = apply[A]((a:A) => M.point[A](a))
}

object CodT {
  /** unit operation of the monad */
  def apply[M[_],A](a : => A)(implicit m : Monad[M]) : CodT[M,A] = new CodT[M,A] {
    def apply[R](k : A => M[R]) : M[R] = k(a)
  }
}

/** Instances satisfied by the Codensity Monad */
trait CodTInstances extends MonadTransSearch[CodT] { self =>
  final def liftM[M[_], A](ma: M[A])(implicit M: MonadSearch[M]): CodT[M, A] = new CodT[M,A] {
      def apply[R](k: (A) => M[R]): M[R] = M.bind[A,R](ma)(k)
    }

   trait MonadTransSearchApply[M[_]] extends MonadSearch[({type λ[α] = CodT[M, α]})#λ] { MT =>
    implicit val M : MonadSearch[M]

    final def point[A](a: => A): CodT[M,A] = CodT[M,A](a)(M)

    final def bind[A, B](fa: CodT[M,A])(f: (A) => CodT[M,B]): CodT[M,B] = new CodT[M,B] {
      def apply[R](k: (B) => M[R]): M[R] = fa[R]((a : A) => f(a)[R](k))
    }

    final def empty[A]: CodT[M,A] = self.liftM[M,A](M.empty[A])
    final def plus[A](ma : CodT[M,A], mb : => CodT[M,A]): CodT[M,A] = new CodT[M,A] {
      lazy val lmb = mb
      def apply[R](k : A => M[R]) : M[R] = M.plus[R]( ma[R](k) , lmb[R](k) )
    }

     final def local[A](ma : CodT[M,A]) : CodT[M,A] = new CodT[M,A] {
      def apply[R](k: (A) => M[R]): M[R] = M.bind[A,R](MT.M.local[A](ma.run))(k)
    }

     final def mtry[A](ma : CodT[M,A], mb : => CodT[M,A]): CodT[M,A] = new CodT[M,A] {
      lazy val lmb = mb
      def apply[R](k : A => M[R]) : M[R] = M.mtry[R]( ma[R](k) , lmb[R](k) )
    }
  }

  implicit def apply[M[_]](implicit pM: MonadSearch[M]): MonadSearch[({type λ[α] = CodT[M, α]})#λ] =
    new MonadTransSearchApply[M] { val M = pM }
}
