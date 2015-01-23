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

import scalaz.Id._
import scalaz.Isomorphism._
import std._
import std.Implicits._


trait EsrevartAble[FD[_],FC[_]] { F =>
  import EsrevartAble._

  def apply[W[_]](implicit W: Esrevart[W]): EsrevartReductible[W,FD,FC]

  final def compose[GD[_],GC[_]](implicit pG: EsrevartAble[GD,GC]): EsrevartAble[({type λ[α] = FD[GD[α]]})#λ, ({type λ[α] = FC[GC[α]]})#λ] =
    new EsrevartAbleCompose[FD, GD, FC, GC] {
      final val F = EsrevartAble.this
      final val G = pG
    }
}

object EsrevartAble {

  trait EsrevartAbleCompose[FD[_], GD[_], FC[_], GC[_]] extends EsrevartAble[({type λ[α] = FD[GD[α]]})#λ, ({type λ[α] = FC[GC[α]]})#λ] { C =>
    implicit val F : EsrevartAble[FD,FC]
    implicit val G : EsrevartAble[GD,GC]

    final def apply[W[_]](implicit W: Esrevart[W]): EsrevartReductible[W, ({type λ[α] = FD[GD[α]]})#λ, ({type λ[α] = FC[GC[α]]})#λ] = {
      object Red extends EsrevartReductible[W, ({type λ[α] = FD[GD[α]]})#λ, ({type λ[α] = FC[GC[α]]})#λ] {

        final val rF: EsrevartReductible[W,FD,FC] = F[W](W)

        type WF[A] = W[rF.Z[A]]
        final val  WF : Esrevart[WF] = W `compose` rF.Z

        val rG: EsrevartReductible[WF,GD,GC] = G[WF](WF)

        type Z[A] = rF.Z[rG.Z[A]]
        final val Z: Esrevart[Z] = rF.Z `compose` rG.Z

        type T[M[_], A] = rG.T[({type λ[α] = rF.T[M, α]})#λ, A]
        final val T: MonadTransSearch[T] = rG.T `compose` rF.T

        def apply[M[_], A,B](implicit M: MonadSearch[M]): (W[FD[GD[A]]] => M[W[FC[GC[B]]]]) <=> (W[Z[A]] => T[M, W[Z[B]]]) =
          new ((W[FD[GD[A]]] => M[W[FC[GC[B]]]]) <=> (W[Z[A]] => T[M, W[Z[B]]])) {
            type FM[X] = rF.T[M, X]
            final val FM: MonadSearch[FM] = rF.T[M](M)

            final val from: (W[Z[A]] => T[M, W[Z[B]]]) => (W[FD[GD[A]]] => M[W[FC[GC[B]]]]) = rF[M, GD[A], GC[B]](M).from `compose` rG[FM, A, B](FM).from
            final val to: (W[FD[GD[A]]] => M[W[FC[GC[B]]]]) => (W[Z[A]] => T[M, W[Z[B]]]) = rG[FM, A, B](FM).to `compose` rF[M, GD[A], GC[B]](M).to
          }

      }
      Red
    }
  }

  def first[pSD, pSC](implicit sdsc: StrategyRel[pSD, pSC]): EsrevartAble[({type λ[α] = (α, pSD)})#λ, ({type λ[α] = (α, pSC)})#λ] = {
    type FD[X] = (X,pSD)
    type FC[X] = (X,pSC)

    new StateEsrevartAble[FD, FC] {
      type Z[X] = Id[X]
      final val  Z = idInstances

      type SD = pSD
      type SC = pSC

      final val stateRel = sdsc

      def domainIso[A]   : FD[A] <=> (Z[A], SD) = new (FD[A] <=> (Z[A], SD)) {
        final val to  : ((A, pSD)) => (Z[A], SD) = Predef.identity[(A,SD)]
        final val from: ((Z[A], SD)) => (A, pSD) = Predef.identity[(A,SD)]
      }

      def codomainIso[A] : FC[A] <=> (Z[A], SC) = new (FC[A] <=> (Z[A], SC)) {
        final val to  : ((A, pSC)) => (Z[A], SC) = Predef.identity[(A,SC)]
        final val from: ((Z[A], SC)) => (A, pSC) = Predef.identity[(A,SC)]
      }

    }
  }

  def second[pSD, pSC](implicit sdsc: StrategyRel[pSD, pSC]): EsrevartAble[({type λ[α] = (pSD,α)})#λ, ({type λ[α] = (pSC,α)})#λ] = {
    type FD[X] = (pSD,X)
    type FC[X] = (pSC,X)

    new StateEsrevartAble[FD, FC] {
      type Z[X] = Id[X]
      final val  Z = idInstances

      type SD = pSD
      type SC = pSC

      final val stateRel = sdsc

      def domainIso[A]   : FD[A] <=> (Z[A], SD) = new (FD[A] <=> (Z[A], SD)) {
        final val to  : ((pSD,A)) => (Z[A], SD) = swapPair[SD,A]
        final val from: ((Z[A], SD)) => (pSD,A) = swapPair[A,SD]
      }

      def codomainIso[A] : FC[A] <=> (Z[A], SC) = new (FC[A] <=> (Z[A], SC)) {
        final val to  : ((pSC,A)) => (Z[A], SC) = swapPair[SC,A]
        final val from: ((Z[A], SC)) => (pSC,A) = swapPair[A,SC]
      }

    }
  }
}

/*
 * State
 */

trait StateEsrevartAble[FD[_], FC[_]] extends EsrevartAble[FD, FC] { F =>
  type Z[_]
  val Z: Esrevart[Z]

  type SD
  type SC

  val stateRel : StrategyRel[SD,SC]

  def domainIso[A]   : FD[A] <=> (Z[A], SD)
  def codomainIso[A] : FC[A] <=> (Z[A], SC)

  final def apply[W[_]](implicit W: Esrevart[W]): EsrevartReductible[W , FD, FC] =
    new EsrevartReductible[W , FD, FC] {
      type Z[A] = F.Z[A]
      final val Z: Esrevart[Z] = F.Z

      final val stateRelW : StrategyRel[W[SD],W[SC]] = stateRel.lift[W](W)

      type T[M[_], A] = StateT[W[SD], W[SC], M, A]
      final val T: MonadTransSearch[T] = stateTInstances[W[SD],W[SC]](stateRelW)

      final def apply[M[_], A,B](implicit M: MonadSearch[M]): (W[FD[A]] => M[W[FC[B]]]) <=> (W[Z[A]] => T[M, W[Z[B]]]) =
        new ((W[FD[A]] => M[W[FC[B]]]) <=> (W[Z[A]] => T[M, W[Z[B]]])) {
          type TM[X] = T[M, X]
          final val TM: MonadSearch[TM] = T[M](M)

          final val to: (W[FD[A]] => M[W[FC[B]]]) => (W[Z[A]] => T[M, W[Z[B]]]) = (r: W[FD[A]] => M[W[FC[B]]]) => (x: W[Z[A]]) => (ws: W[SD]) =>
              M.apply(r(W.map(W.zip(x, ws))(domainIso[A].from)))((wfa: W[FC[B]]) => {
                val wzs = W.map(wfa)(codomainIso[B].to)
                (W.map(wzs)(_._1), W.map(wzs)(_._2))
              })

          final val from: (W[Z[A]] => T[M, W[Z[B]]]) => (W[FD[A]] => M[W[FC[B]]]) = (r: W[Z[A]] => T[M, W[Z[B]]]) => (x: W[FD[A]]) => {
              val wzs: W[(Z[A], SD)] = W.map(x)(domainIso[A].to)
              M.apply(r(W.map(wzs)(_._1))(W.map(wzs)(_._2)))((p: (W[Z[B]], W[SC])) =>
                W.map(W.zip(p._1, p._2))(codomainIso[B].from)
              )
            }
        }
    }
}


object StateEsrevartAble {
  final def apply[pZ[_], pSD, pSC](implicit pZ: Esrevart[pZ], pStateRel : StrategyRel[pSD,pSC]): StateEsrevartAble[({type λ[α] = (pZ[α], pSD)})#λ,({type λ[α] = (pZ[α], pSC)})#λ] =
    new StateEsrevartAble[({type λ[α] = (pZ[α], pSD)})#λ,({type λ[α] = (pZ[α], pSC)})#λ] {
      type Z[A] = pZ[A]
      final val Z: Esrevart[Z] = pZ

      type SD = pSD
      type SC = pSC
      final val stateRel : StrategyRel[SD,SC] = pStateRel


      def domainIso[A]: (Z[A], SD) <=> (Z[A], SD) = new ((Z[A], SD) <=> (Z[A], SD)) {
        final val to: ((Z[A], SD)) => (Z[A], SD) = Predef.identity[(Z[A], SD)]
        final val from: ((Z[A], SD)) => (Z[A], SD) = Predef.identity[(Z[A], SD)]
      }

      def codomainIso[A]: (Z[A], SC) <=> (Z[A], SC) = new ((Z[A], SC) <=> (Z[A], SC)) {
        final val to: ((Z[A], SC)) => (Z[A], SC) = Predef.identity[(Z[A], SC)]
        final val from: ((Z[A], SC)) => (Z[A], SC) = Predef.identity[(Z[A], SC)]
      }
    }
}

