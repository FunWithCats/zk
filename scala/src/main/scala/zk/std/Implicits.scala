package zk.std

import zk._
import zk.syntax.MonadSearchOps

import scalaz.syntax.{MonadPlusOps, BindOps, FunctorOps}

/** Useful implicit definitions */
object Implicits {
  implicit object codTInstances                                              extends CodTInstances
  implicit object slCodTInstances                                            extends SLCodTInstances
  implicit def    contTInstances[R]                                          = new ContTInstances[R] {}
  implicit object idInstances                                                extends IdInstances
  implicit object idTInstances                                               extends IdTInstances
  implicit def    firstInstances[B]                                          = new   FirstInstances[B] { }
  implicit object anyMonadSearch                                                 extends AnyMonadSearchInstances {}
  implicit object listInstances                                              extends ListInstances
  implicit def    listInstances1[A]                                          = new   ListInstances1[A] { }
  implicit object logTInstances                                              extends LogTInstances
  implicit object optionInstances                                            extends OptionInstances
  implicit object slOptionInstances                                          extends SLOptionInstances
  implicit object pairInstances                                              extends PairInstances
  implicit def    secondInstances[B]                                         = new   SecondInstances[B] { }
  implicit def    stateTInstances[SC,SD](implicit scsd : StrategyRel[SC,SD]) = new   StateTInstances[SC,SD] { val stateRel = scsd }
  implicit object streamInstances                                            extends StreamInstances
  implicit def    treeMapInstances[K](implicit pK : Ordering[K])             = new   TreeMapInstances[K] { val KeysOrdering = pK }
  implicit def    treeMapInstances1[K,A](implicit pK : Ordering[K])          = new   TreeMapInstances1[K,A] { val KeysOrdering = pK }

  implicit val codOptionInstances     = codTInstances[Option](optionInstances)
  implicit val codListInstances       = codTInstances[List](listInstances)
  implicit val slCodOptionSLInstances = slCodTInstances[SLOption](slOptionInstances)
  implicit val slCodListSLInstances   = slCodTInstances[List](listInstances)

  /*
   * Congruence Monad
   */

  implicit def congruenceMonadToRotareti[X,Y,B](cm : CongruenceMonad[X,Y,B,B]) : AnyMonadSearch[Rotareti[AnyMonadSearch,X,Y,B]] =
    cm((b:B) => anyMonadSearch.point(Answer[AnyMonadSearch,X,Y,B](b)))

  implicit def congruenceMonadToFunctorOps[X,Y,B,α](cm : CongruenceMonad[X,Y,B,α]) : FunctorOps[({ type λ[α] = CongruenceMonad[X,Y,B,α] })#λ, α] =
    congruenceMonad[X,Y,B].functorSyntax.ToFunctorOps[α](cm)

  implicit def congruenceMonadToBindOps[X,Y,B,α](cm : CongruenceMonad[X,Y,B,α]) : BindOps[({ type λ[α] = CongruenceMonad[X,Y,B,α] })#λ, α] =
    congruenceMonad[X,Y,B].bindSyntax.ToBindOps[α](cm)

  implicit def congruenceMonadToMonadPlusOps[X,Y,B,α](cm : CongruenceMonad[X,Y,B,α]) : MonadPlusOps[({ type λ[α] = CongruenceMonad[X,Y,B,α] })#λ, α] =
    congruenceMonad[X,Y,B].monadPlusSyntax.ToMonadPlusOps[α](cm)

  implicit def congruenceMonadToMonadSearchOps[X,Y,B,α](cm : CongruenceMonad[X,Y,B,α]) : MonadSearchOps[({ type λ[α] = CongruenceMonad[X,Y,B,α] })#λ, α] =
    congruenceMonad[X,Y,B].monadSearchSyntax.ToMonadSearchOps[α](cm)

  implicit def congruenceMonadToELens[A,X,Y,B](f : A => CongruenceMonad[X,Y,B,B])(implicit default : X => AnyMonadSearch[Y]) : ELens[AnyMonadSearch, A, X, Y, B] =
    ELens[AnyMonadSearch,A,X,Y,B]( (a:A) => f(a)((b:B) => anyMonadSearch.point(Answer[AnyMonadSearch,X,Y,B](b))) ,  default)
}
