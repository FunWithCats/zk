package zk

import scala.language.higherKinds
import scala.language.implicitConversions

import scalaz.Free.Trampoline
import zk.std.Implicits._

package object std {

  type IdT[M[_],A] = M[A]
  type Pair[A] = (A, A)
  type StateT[SD, SC, M[_] , A] = SD => M[(A,SC)]
  type ContT[R,F[_],A] = (A => F[R]) => F[R]
  type SLOption[X] = Trampoline[Option[X]]


  type CodOption[A]   = CodT[Option,A]
  type CodList[A]     = CodT[List,A]
  type SLCodOption[A] = SLCodT[SLOption,A]
  type SLCodList[A]   = SLCodT[List,A]

  /*
   * Congruence Monad
   */

  type CongruenceMonad[X, Y, B, α] = ContT[Rotareti[AnyMonadSearch, X, Y, B], AnyMonadSearch , α]

  def congruenceMonad[X,Y,B] : MonadSearch[({ type λ[α] = CongruenceMonad[X,Y,B,α] })#λ] =
    contTInstances[Rotareti[AnyMonadSearch,X,Y,B]][AnyMonadSearch](anyMonadSearch)

  def rewrite[X,Y,B](x : X) : CongruenceMonad[X,Y,B,Y] =
    (k : Y => AnyMonadSearch[Rotareti[AnyMonadSearch,X,Y,B]]) => anyMonadSearch.point(Focus[AnyMonadSearch,X,Y,B](x , k))

  def rewriteEndo[X,B](x : X) : CongruenceMonad[X,X,B,X] = rewrite[X,X,B](x)
}
