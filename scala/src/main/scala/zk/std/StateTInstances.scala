package zk.std

import zk.{MonadTransSearch, MonadSearch, StrategyRel}

trait StateTInstances[SD,SC] extends MonadTransSearch[({type λ[α[_],β] = StateT[SD,SC,α,β]})#λ] { self =>
  val stateRel : StrategyRel[SD,SC]

  def liftM[M[_], A](ma: M[A])(implicit M: MonadSearch[M]): StateT[SD,SC,M,A] =
    (sd : SD) => M.bind[A,(A,SC)](ma)((a : A) => M.apply[SC,(A,SC)](stateRel.to[M](sd)(M))( (sc : SC) => (a,sc)))

  trait MonadTransSearchApply[M[_]] extends MonadSearch[({type λ[α] = StateT[SD,SC,M,α]})#λ] {
    implicit val M : MonadSearch[M]

    def point[A](a: => A): StateT[SD,SC,M,A] = self.liftM[M,A](M.point[A](a))(M)

    def bind[A, B](fa: StateT[SD,SC,M,A])(f: (A) => StateT[SD,SC,M,B]): StateT[SD,SC,M,B] =
      (sd : SD) => M.bind[(A,SC),(B,SC)](fa(sd))((p : (A,SC)) => M.bind[SD, (B,SC)](stateRel.from[M](p._2)(M))(f(p._1)))

    def empty[A]: StateT[SD,SC,M,A] = self.liftM[M,A](M.empty[A])
    def plus[A](a : StateT[SD,SC,M,A], b: => StateT[SD,SC,M,A]): StateT[SD,SC,M,A] = (sd : SD) => M.plus[(A,SC)](a(sd) , b(sd))

    def local[A](ma : StateT[SD,SC,M,A]) : StateT[SD,SC,M,A] = (sd : SD) => M.local(ma(sd))
    def mtry[A](a : StateT[SD,SC,M,A], b: => StateT[SD,SC,M,A]): StateT[SD,SC,M,A] = (sd : SD) => M.mtry[(A,SC)](a(sd) , b(sd))

    override def mif[A,B](cond : StateT[SD,SC,M,A], mt : => StateT[SD,SC,M,B], me : => StateT[SD,SC,M,B]) : StateT[SD,SC,M,B] =
      (sd : SD) => M.mif[(A,SC),(B,SC)](cond(sd), mt(sd), me(sd))
  }

  override implicit def apply[M[_]](implicit pM: MonadSearch[M]): MonadSearch[({type λ[α] = StateT[SD,SC,M,α]})#λ] =
    new MonadTransSearchApply[M] { val M = pM }
}
