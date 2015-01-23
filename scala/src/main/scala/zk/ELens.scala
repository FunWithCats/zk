/*
   Copyright (c) 2012-2014, Université de Lorraine, Nancy, France
   Copyright (c) 2014-2015, Christophe Calvès

   All rights reserved.
   
   Redistribution and use in source and binary forms, with or without
   modification, are permitted provided that the following conditions are met:
   
   * Redistributions of source code must retain the above copyright notice, this
     list of conditions and the following disclaimer.
   
   * Redistributions in binary form must reproduce the above copyright notice,
     this list of conditions and the following disclaimer in the documentation
     and/or other materials provided with the distribution.
   
   * Neither the name of Université de Lorraine nor the names of its
     contributors may be used to endorse or promote products derived from
     this software without specific prior written permission.
   
   THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
   AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
   IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
   DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE
   FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
   DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
   SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
   CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,
   OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
   OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
*/

package zk

import scalaz.{Monad, NaturalTransformation, MonadTrans}


/** An iterator whose next value of type X (the '''focus''') is computed in the monad M
 *  using a '''parameter''' of type Y. When there is no next value, it gives
 *  an end value (the '''answer''') of type B.
 *
 * @tparam M monad the computation is living in.
 * @tparam X values of the iterator.
 * @tparam Y parameter for next values.
 * @tparam B end result.
 */
sealed abstract class Rotareti[M[_],X,Y,B] {

  /** Uses ''f'' to run the iterator until there is no more focus.
   *
   * @param f compute the parameter Y from present focus X.
   * @return the anwser (final value when there is no more focus).
   */
  def getAnswer(f : X => M[Y]) : M[B]

  /** Lifts the monad the computation of next focus is living in by the monad transformer T */
  def lift[T[_[_],_]](implicit T : MonadTrans[T]) : Rotareti[({type λ[α] = T[M,α]})#λ,X,Y,B]

  /** Attaches a transformation to the focuses and parameters of the iterator.
    *
    * @param domain   transformation of focuses.
    * @param codomain transformation of parameters.
    * @tparam R       type of the ''new'' focuses.
    * @tparam S       type of the ''new'' parameters.
    */
  def refocus[R,S](domain : X => R, codomain : S => M[Y]) : Rotareti[M,R,S,B]

  /** Replaces the monad the computation is living in (M) by another monad (N) using
   * a natural transformation.
   *
   * @param  nat natural transformation from M to N.
   * @param  N   evidence that N is a monad.
   * @tparam N   new monad for the computation.
   * @return transformed iterator.
   */
  def transform[N[_]](nat : NaturalTransformation[M,N])(implicit N : Monad[N]) : Rotareti[N,X,Y,B]

  /** Is this iterator an [[Answer]] (true) or a [[Focus]] (false). */
  def isAnswer : Boolean
}

/** Case where there is no more focus in the iterator but an end value ''answer''.
 *
 * @param  answer end value of the iterator.
 * @param  M
 * @tparam M monad the computation is living in.
 * @tparam X values of the iterator.
 * @tparam Y parameter for next values.
 * @tparam B type of ''answer''.
 */
final case class Answer[M[_],X,Y,B](val answer : B)(implicit M : Monad[M])  extends Rotareti[M,X,Y,B] {
  /** Returns ''answer''. */
  def getAnswer(f : X => M[Y]) : M[B] = M.point[B](answer)

  /** Lifts the monad the computation of next focus is living in by the monad transformer T */
  def lift[T[_[_],_]](implicit T : MonadTrans[T]) : Answer[({type λ[α] = T[M,α]})#λ,X,Y,B] = {
    type TM[Z] = T[M,Z]
    val  TM : Monad[TM] = T[M](M)
    Answer[TM,X,Y,B](answer)(TM)
  }

  /** Attaches a transformation to the focuses and parameters of the iterator.
    *
    * @param domain   transformation of focuses.
    * @param codomain transformation of parameters.
    * @tparam R       type of the ''new'' focuses.
    * @tparam S       type of the ''new'' parameters.
    */
  def refocus[R,S](domain : X => R, codomain : S => M[Y]) : Answer[M,R,S,B] = Answer[M,R,S,B](answer)

  /** Replaces the monad the computation is living in (M) by another monad (N) using
    * a natural transformation.
    *
    * @param  nat natural transformation from M to N.
    * @param  N   evidence that N is a monad.
    * @tparam N   new monad for the computation.
    * @return transformed iterator.
    */
  def transform[N[_]](nat : NaturalTransformation[M,N])(implicit N : Monad[N]) : Answer[N,X,Y,B] =
    Answer[N,X,Y,B](answer)(N)

  /** true */
  val isAnswer : Boolean = true
}


/**
 * 
 * @param focus
 * @param context
 * @param M
 * @tparam M monad the computation is living in.
 * @tparam X values of the iterator.
 * @tparam Y parameter for next values.
 * @tparam B end result.
 */
final case class Focus[M[_],X,Y,B](val focus : X, val context : Y => M[Rotareti[M,X,Y,B]])(implicit M : Monad[M]) extends Rotareti[M,X,Y,B] {
  import M.monadSyntax._

  /** A loop that computes the next step using ''f''(''focus'') as parameter.
    *
    * @param f compute the parameter Y from focus''.
    * @return the anwser (final value when there is no more focus).
    */
  def getAnswer(f : X => M[Y]) : M[B] = f(focus) >>= context >>= (_.getAnswer(f))

  /** Lifts the monad the computation of next focus is living in by the monad transformer T */
  def lift[T[_[_],_]](implicit T : MonadTrans[T]) : Focus[({type λ[α] = T[M,α]})#λ,X,Y,B] = {
    type TM[Z] = T[M,Z]
    val  TM : Monad[TM] = T[M](M)
    Focus[TM,X,Y,B](focus, (y:Y) => T.liftM[M,Rotareti[TM,X,Y,B]](M.apply(context(y))(_.lift[T](T))))(TM)
  }

  /** Attaches a transformation to the focuses and parameters of the iterator.
    *
    * @param domain   transformation of ''focus''.
    * @param codomain transformation of parameters.
    * @tparam R       type of the ''new'' focuses.
    * @tparam S       type of the ''new'' parameters.
    */
  def refocus[R,S](domain : X => R, codomain : S => M[Y]) : Focus[M,R,S,B] = Focus[M,R,S,B](domain(focus), (s:S) => M.apply(M.bind(codomain(s))(context))(_.refocus(domain,codomain)))

  /** Replaces the monad the computation is living in (M) by another monad (N) using
    * a natural transformation.
    *
    * @param  nat natural transformation from M to N.
    * @param  N   evidence that N is a monad.
    * @tparam N   new monad for the computation.
    * @return transformed iterator.
    */
  def transform[N[_]](nat : NaturalTransformation[M,N])(implicit N : Monad[N]) : Focus[N,X,Y,B] =
    Focus[N,X,Y,B](focus, (y:Y) => nat(M.apply(context(y))(_.transform[N](nat)(N))))(N)

  /** false */
  val isAnswer : Boolean = false
}


object Rotareti {
  /** Replaces the monad the computation is living in (M) by another monad (N) using
    * a natural transformation.
    *
    * @param  mr  the iterator to transform.
    * @param  nat natural transformation from M to N.
    * @param  M   evidence that M is a monad.
    * @param  N   evidence that N is a monad.
    * @tparam M   present monad of mr.
    * @tparam N   new monad for the computation.
    * @return transformed iterator.
    */
  def transform[M[_],N[_],X,Y,B](mr : M[Rotareti[M,X,Y,B]], nat : NaturalTransformation[M,N])(implicit M : Monad[M], N : Monad[N]) : N[Rotareti[N,X,Y,B]] =
    nat[Rotareti[N,X,Y,B]](M.apply(mr)(_.transform[N](nat)(N)))
}


/** Transforms A to B giving focuses of type X in the process and expecting parameters of type Y.
 * Focuses can be seen as requests made by the transformation and parameters as responses to these requests.
 *
 * ''default'' is used as a fallback transformation from X to Y when needed.
 *
 * For example:
 * In order to transform a term of type A, the transformation could give as focuses its subterms of type X.
 * It would expect as parameters subterms of B.
 */
case class ELens[M[_],A,X,Y,B](val lens : A => M[Rotareti[M,X,Y,B]] , val default : X => M[Y]) extends (A => M[Rotareti[M,X,Y,B]]) {
  /** Just ''lens'' */
  final def apply(a:A) : M[Rotareti[M,X,Y,B]] = lens(a)
}

/** An iterator with exactly one focus on the Identity monad. */
case class Context[X,Y,B](val focus : X, val context : Y => B) {
  /** Transforms this iterator into a [[Rotareti]] */
  final def toRotareti[F[_]](implicit F : Monad[F]) : Rotareti[F,X,Y,B] = Focus[F,X,Y,B](focus , (y:Y) => F.point(Answer[F,X,Y,B](context(y))))
}
