package zk.std

import zk.{MonadTransSearch, MonadSearch}

/** Instances of the Continuation Monad Transformer */
trait ContTInstances[R] extends MonadTransSearch[({type λ[α[_],β] = ContT[R,α,β]})#λ] { self =>
  final def liftM[M[_], A](ma: M[A])(implicit M: MonadSearch[M]): ContT[R,M,A] = M.bind[A,R](ma)

  trait MonadTransSearchApply[M[_]] extends MonadSearch[({type λ[α] = ContT[R,M,α]})#λ] { MT =>
    implicit val M : MonadSearch[M]

    final def point[A](a: => A): ContT[R,M,A] = (k : A => M[R]) => k(a)

    final def bind[A, B](fa: ContT[R,M,A])(f: (A) => ContT[R,M,B]): ContT[R,M,B] = (k: (B) => M[R]) => fa((a : A) => f(a)(k))

    final def empty[A]: ContT[R,M,A] = self.liftM[M,A](M.empty[A])
    final def plus[A](ma : ContT[R,M,A], mb : => ContT[R,M,A]): ContT[R,M,A] = (k : A => M[R]) => M.plus[R]( ma(k) , mb(k) )

    final def local[A](ma : ContT[R,M,A]) : ContT[R,M,A] = (k: (A) => M[R]) => MT.M.local[R](ma(k))

    final def mtry[A](ma : ContT[R,M,A], mb : => ContT[R,M,A]): ContT[R,M,A] = (k : A => M[R]) => M.mtry[R]( ma(k) , mb(k) )
  }

  final implicit def apply[M[_]](implicit pM: MonadSearch[M]): MonadSearch[({type λ[α] = ContT[R,M, α]})#λ] =
    new MonadTransSearchApply[M] { val M = pM }
}
