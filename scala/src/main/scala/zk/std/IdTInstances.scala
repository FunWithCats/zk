package zk.std

import zk.{MonadTransSearch, MonadSearch}

trait IdTInstances extends MonadTransSearch[IdT] {
  def liftM[M[_], A](a: M[A])(implicit m: MonadSearch[M]): IdT[M, A] = a
  override implicit def apply[M[_]](implicit M: MonadSearch[M]): MonadSearch[({type λ[α] = IdT[M, α]})#λ] = M
  override def compose[G[_[_],_]](implicit G : MonadTransSearch[G]) : MonadTransSearch[({type λ[α[_],β] = IdT[({type λ[β] = G[α,β]})#λ , β]})#λ] = G
}
