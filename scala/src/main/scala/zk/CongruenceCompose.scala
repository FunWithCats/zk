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

package zk {

import scalaz.Equal

/** Type class for composition of [[Congruence]]-like entities.
    * They can be seen as arrows whose domain and codomain are both of functional types (
    * so with two type parameters).
    *
    * F[X,Y,A,B] represents an arrow from [X,Y] to [A,B] where [X,Y] (resp. [A,B]) means anything parametrized by
    * X and Y (resp. A and B).
    *
    * @tparam F [[Congruence]]-like type constructor.
    */
  trait CongruenceCompose[F[_, _, _, _]] {
    import syntax._

    /** identity arrow */
    def id[X, Y]: F[X, Y, X, Y]

    /** Lazy composition of two congruence-like ''g'' : [X,Y] => [A,B] and ''f'' : [A,B] => [R,S] : ''f'' o ''g'' */
    def lConCompose[X, Y, A, B, R, S](f: => F[A, B, R, S], g: => F[X, Y, A, B]): F[X, Y, R, S]

    /** Lifts domains by the functor (_,R) and codomains by (_,S).
      *
      * It must exist a strategy relation between R and S.
      */
    def conFirst[X, Y, A, B, R, S](f: F[X, Y, A, B])(implicit rs: StrategyRel[R, S]): F[(X, R), (Y, S), (A, R), (B, S)]

    /** Lifts domains by the functor (R,_) and codomains by (S,_)
      *
      * It must exist a strategy relation between R and S.
      */
    def conSecond[X, Y, A, B, R, S](f: F[X, Y, A, B])(implicit rs: StrategyRel[R, S]): F[(R, X), (S, Y), (R, A), (S, B)]

    /** Lazy composition of two congruence-like ''g'' : [X,Y] => [A,B] and ''f'' : [A,B] => [R,S] : ''g'' o ''f'' */
    final def conAndThen[X, Y, A, B, R, S](f: => F[X, Y, A, B], g: => F[A, B, R, S]): F[X, Y, R, S] = lConCompose[X, Y, A, B, R, S](g, f)

    /** Composition of two congruence-like ''g'' : [X,Y] => [A,B] and ''f'' : [A,B] => [R,S] : ''f'' o ''g'' */
    final def conCompose[X, Y, A, B, R, S](f: F[A, B, R, S], g: F[X, Y, A, B]): F[X, Y, R, S] = lConCompose[X, Y, A, B, R, S](f, g)


    /** Product of two congruence-like ''f'' : [X1,Y1] => [A1,B1] and ''g'' : [X2,Y2] => [A2,B2] to produce
      * a congruence-like [(X1,X2) , (Y1,Y2)] => [(A1,A2) , (B1,B2)].
      *
      * It must exists a strategy relation between A1 and B1 and between X2 and Y2.
      */
    final def conProdL[X1, X2, Y1, Y2, A1, A2, B1, B2](f: => F[X1, Y1, A1, B1], g: => F[X2, Y2, A2, B2])(implicit a1b1: StrategyRel[A1, B1], x2y2: StrategyRel[X2, Y2]): F[(X1, X2), (Y1, Y2), (A1, A2), (B1, B2)] =
      lConCompose[(X1, X2), (Y1, Y2), (A1, X2), (B1, Y2), (A1, A2), (B1, B2)](conSecond[X2, Y2, A2, B2, A1, B1](g)(a1b1), conFirst[X1, Y1, A1, B1, X2, Y2](f)(x2y2))

    /** Product of two congruence-like ''f'' : [X1,Y1] => [A1,B1] and ''g'' : [X2,Y2] => [A2,B2] to produce
      * a congruence-like [(X1,X2) , (Y1,Y2)] => [(A1,A2) , (B1,B2)].
      *
      * It must exists a strategy relation between A2 and B2 and between X1 and Y1.
      */
    final def conProdR[X1, X2, Y1, Y2, A1, A2, B1, B2](f: => F[X1, Y1, A1, B1], g: => F[X2, Y2, A2, B2])(implicit x1y1: StrategyRel[X1, Y1], a2b2: StrategyRel[A2, B2]): F[(X1, X2), (Y1, Y2), (A1, A2), (B1, B2)] =
      lConCompose[(X1, X2), (Y1, Y2), (X1, A2), (Y1, B2), (A1, A2), (B1, B2)](conFirst[X1, Y1, A1, B1, A2, B2](f)(a2b2), conSecond[X2, Y2, A2, B2, X1, Y1](g)(x1y1))


    /*
     * SYNTAX
     */

    /** syntax helper */
    object congruenceComposeSyntax extends CongruenceComposeSyntax[F] {
      final val F = CongruenceCompose.this
    }

    /*
     * LAWS
     */

    /** Laws on CongruenceCompose */
    trait CongruenceComposeLaw {
      /** ''id'' o ''f'' = ''f'' */
      def idLeft[X,Y,A,B](f:F[X,Y,A,B])(implicit F1 : Equal[F[X,Y,A,B]]) : Boolean = F1.equal(lConCompose(id[A,B], f), f)

      /** ''f'' o ''id'' = ''f'' */
      def idRight[X,Y,A,B](f:F[X,Y,A,B])(implicit F1 : Equal[F[X,Y,A,B]]) : Boolean = F1.equal(lConCompose(f , id[X,Y]), f)

      /** ''f'' o (''g'' o ''h'') = (''f'' o ''g'') o ''h'' */
      def lComposeAssociative[X,Y,A,B,R,S,W,T](f:F[R,S,W,T], g:F[A,B,R,S], h:F[X,Y,A,B])(implicit F1 : Equal[F[X,Y,W,T]]) : Boolean =
        F1.equal(lConCompose(f,lConCompose(g,h)), lConCompose(lConCompose(f,g), h))
    }

    def congruenceComposeLaw = new CongruenceComposeLaw { }
  }

  object CongruenceCompose {
    def apply[F[_, _, _, _]](implicit F: CongruenceCompose[F]): CongruenceCompose[F] = F
  }
}

package zk.syntax {

  import zk._

  /** Operations on a CongruenceCompose instance */
  final case class CongruenceComposeOps[F[_, _, _, _], X, Y, A, B](val self: F[X, Y, A, B])(implicit val F: CongruenceCompose[F]) {
    /** Lazy composition : '''self''' o ''g'' */
    def lConCompose[R, S](g: => F[R, S, X, Y]): F[R, S, A, B] = F.lConCompose[R, S, X, Y, A, B](self, g)

    /** alias for lConCompose */
    def <==<[R, S](g: => F[R, S, X, Y]): F[R, S, A, B] = F.lConCompose[R, S, X, Y, A, B](self, g)

    /** Lifts domains by the functor (_,R) and codomains by (_,S).
      *
      * It must exist a strategy relation between R and S.
      */
    def conFirst[R, S](implicit rs: StrategyRel[R, S]): F[(X, R), (Y, S), (A, R), (B, S)] = F.conFirst[X, Y, A, B, R, S](self)(rs)

    /** Lifts domains by the functor (R,_) and codomains by (S,_)
      *
      * It must exist a strategy relation between R and S.
      */
    def conSecond[R, S](implicit rs: StrategyRel[R, S]): F[(R, X), (S, Y), (R, A), (S, B)] = F.conSecond[X, Y, A, B, R, S](self)(rs)

    /** Lazy composition : ''g'' o '''self''' */
    def conAndThen[R, S](g: => F[A, B, R, S]): F[X, Y, R, S] = F.lConCompose[X, Y, A, B, R, S](g, self)

    /** alias for conAndThen */
    def >==>[R, S](g: => F[A, B, R, S]): F[X, Y, R, S] = F.lConCompose[X, Y, A, B, R, S](g, self)

    /** Composition : '''self''' o ''g'' */
    def conCompose[R, S](g: F[R, S, X, Y]): F[R, S, A, B] = F.lConCompose[R, S, X, Y, A, B](self, g)

    /** Product by a congruence-like ''g'' : [X2,Y2] => [A2,B2] to produce
      * a congruence-like [(X,X2) , (Y,Y2)] => [(A,A2) , (B,B2)].
      *
      * It must exists a strategy relation between A and B and between X2 and Y2.
      */
    def ~***[X2, Y2, A2, B2](g: => F[X2, Y2, A2, B2])(implicit ab: StrategyRel[A, B], x2y2: StrategyRel[X2, Y2]): F[(X, X2), (Y, Y2), (A, A2), (B, B2)] = F.conProdL[X, X2, Y, Y2, A, A2, B, B2](self, g)(ab, x2y2)

    /** Product by a congruence-like ''g'' : [X2,Y2] => [A2,B2] to produce
      * a congruence-like [(X,X2) , (Y,Y2)] => [(A,A2) , (B,B2)].
      *
      * It must exists a strategy relation between A2 and B2 and between X and Y.
      */
    def ***~[X2, Y2, A2, B2](g: => F[X2, Y2, A2, B2])(implicit xy: StrategyRel[X, Y], a2b2: StrategyRel[A2, B2]): F[(X, X2), (Y, Y2), (A, A2), (B, B2)] = F.conProdR[X, X2, Y, Y2, A, A2, B, B2](self, g)(xy, a2b2)
  }

  trait ToCongruenceComposeOps {
    final implicit def ToCongruenceComposeOps[F[_, _, _, _], X, Y, A, B](v: F[X, Y, A, B])(implicit F: CongruenceCompose[F]) = new CongruenceComposeOps[F, X, Y, A, B](v)(F)
  }

  trait CongruenceComposeSyntax[F[_, _, _, _]] {
    val F: CongruenceCompose[F]

    final implicit def ToCongruenceComposeOps[X, Y, A, B](v: F[X, Y, A, B]): CongruenceComposeOps[F, X, Y, A, B] = new CongruenceComposeOps[F, X, Y, A, B](v)(CongruenceComposeSyntax.this.F)
  }

}
