package zk.std


import scalaz.{Applicative, Traverse, Comonad}

trait FirstInstances[B] extends Comonad[({type λ[α] = (α, B)})#λ] with Traverse[({ type λ[α] = (α, B) })#λ] {
  def copoint[A](p: (A, B)): A = p._1

  def cobind[A, C](fa: (A, B))(f: ((A, B)) => C): (C, B) = (f(fa), fa._2)

  override def cojoin[A](fa: (A, B)): ((A, B), B) = (fa, fa._2)

  def traverseImpl[G[_],A,C](fa : (A,B))(f : A => G[C])(implicit G : Applicative[G]) : G[(C,B)] = G.map(f(fa._1))(c => (c, fa._2))
}

trait SecondInstances[B] extends Comonad[({type λ[α] = (B, α)})#λ] with Traverse[({ type λ[α] = (B, α) })#λ] {
  def copoint[A](p: (B, A)): A = p._2

  def cobind[A, C](fa: (B, A))(f: ((B, A)) => C): (B, C) = (fa._1, f(fa))

  override def cojoin[A](fa: (B, A)): (B, (B, A)) = (fa._1, fa)

  def traverseImpl[G[_],A,C](fa : (B,A))(f : A => G[C])(implicit G : Applicative[G]) : G[(B,C)] = G.map(f(fa._2))(c => (fa._1,c))
}
