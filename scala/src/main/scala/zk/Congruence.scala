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

import scalaz._
import scalaz.Id._

import scala.util.Random

import zk.std._
import zk.std.Implicits._
import zk.syntax._
import zk.Implicits._

/** Represents Strategy transformations.
 *  Essentially forall F:[[Esrevart]],M:[[MonadSearch]]. (F[X] => M[F[Y]]) => F[A] => M[F[B]]
 */
trait Congruence[X, Y, A, B] extends ((=> Strategy[X,Y]) => Strategy[A,B]) { self =>

  import Congruence._

  /** The transformation */
  def apply[F[_], M[_]](r: F[X] => M[F[Y]])(implicit F: Esrevart[F], M : MonadSearch[M]) : F[A] => M[F[B]]

  /*
   * Applications
   */

  /** Transformations with F = Id */
  final def apply[M[_]](r : X => M[Y])(implicit M : MonadSearch[M]) : A => M[B] = self[Id,M](r)(idInstances, M)

  /** Transformation on strategies */
  final def apply[F[_]](r: => Strategy[F[X], F[Y]])(implicit F: Esrevart[F]): Strategy[F[A],F[B]] = new Strategy[F[A],F[B]] {
    lazy val pr = r
    def apply[M[_]](implicit M: MonadSearch[M]): F[A] => M[F[B]] = self[F,M](pr[M](M))(F,M)
  }

  /** Transformations on strategies with F = Id */
  final def apply(r: => Strategy[X,Y]): Strategy[A,B] = new Strategy[A,B] {
    lazy val pr = r
    def apply[M[_]](implicit M: MonadSearch[M]): A => M[B] = self[Id,M](pr[M](M))(idInstances,M)
  }

  /** Transformation with F being an [[EsrevartAble]] */
  def apply[FD[_], FC[_], M[_]](r: FD[X] => M[FC[Y]])(implicit F: EsrevartAble[FD,FC], M : MonadSearch[M]): FD[A] => M[FC[B]] = {
    val rF : EsrevartReductible[Id,FD,FC] = F[Id](idInstances)

    type TM[X] = rF.T[M,X]
    val  TM : MonadSearch[TM] = rF.T[M](M)

    val r2 : rF.Z[X] => TM[rF.Z[Y]] = rF[M,X,Y](M).to(r)
    val r3 : rF.Z[A] => TM[rF.Z[B]] = self[rF.Z, TM](r2)(rF.Z, TM)

    rF[M,A,B](M).from(r3)
  }


  /** Transformation on strategies with F being an [[EsrevartAble]] */
  final def apply[FD[_],FC[_]](r: => Strategy[FD[X],FC[Y]])(implicit F: EsrevartAble[FD,FC]): Strategy[FD[A],FC[B]] = new Strategy[FD[A],FC[B]] {
    lazy val pr = r
    implicit def apply[M[_]](implicit M: MonadSearch[M]): FD[A] => M[FC[B]] = self[FD,FC,M](pr[M](M))(F,M)
  }

  /*
   * Functors
   */


  final def liftTraverse[G[_]](atob : Strategy[A,B])(implicit G: Traverse[G]): Congruence[X,Y,G[A],G[B]] =
    congruenceInstances.lConCompose(traverseToCongruence[G,A,B](atob)(G), self)

  final def esrevart[G[_]](implicit G: Esrevart[G]): Congruence[G[X],G[Y],G[A],G[B]] = new Congruence[G[X],G[Y],G[A],G[B]] {
    def apply[F[_], M[_]](r: F[G[X]] => M[F[G[Y]]])(implicit F: Esrevart[F], M : MonadSearch[M]): F[G[A]] => M[F[G[B]]] = {
      self[({type λ[α] = F[G[α]]})#λ, M](r)(F `compose` G, M)
    }
  }

  final def esrevartAble[GD[_],GC[_]](implicit G: EsrevartAble[GD,GC]): Congruence[GD[X], GC[Y], GD[A], GC[B]] = new Congruence[GD[X] ,GC[Y], GD[A], GC[B]] {
    def apply[F[_], M[_]](r: F[GD[X]] => M[F[GC[Y]]])(implicit F: Esrevart[F], M : MonadSearch[M]): F[GD[A]] => M[F[GC[B]]] = {
      val rG: EsrevartReductible[F,GD,GC] = G[F](F)

      type TM[X] = rG.T[M,X]
      val TM : MonadSearch[TM] = rG.T[M](M)

      type FZ[X] = F[rG.Z[X]]
      val  FZ : Esrevart[FZ] = F `compose` rG.Z

      val r2 : FZ[X] => TM[FZ[Y]] = rG[M,X,Y](M).to(r)
      val r3 : FZ[A] => TM[FZ[B]] = self[FZ, TM](r2)(FZ,TM)
      rG[M,A,B](M).from(r3)
    }

    override def apply[FD[_], FC[_], M[_]](r: FD[GD[X]] => M[FC[GC[Y]]])(implicit F: EsrevartAble[FD,FC], M : MonadSearch[M]): FD[GD[A]] => M[FC[GC[B]]] = {
      self[({type λ[α] = FD[GD[α]]})#λ, ({type λ[α] = FC[GC[α]]})#λ, M](r)(F `compose` G, M)
    }
  }

  /** Trace the congruence printing log to standard output
   *
   * @param name given to this Congruence in the trace.
   * @return
   */
  def trace(name: String): Congruence[X,Y,A,B] = new Congruence[X,Y,A,B] {
    def apply[F[_], M[_]](r: F[X] => M[F[Y]])(implicit F: Esrevart[F], M:MonadSearch[M]): F[A] => M[F[B]] = {
      val rnd  : Int    = Random.nextInt()

      val id   : String = name + "-" + rnd

      val rr   : F[X] => M[F[Y]] = (fx : F[X]) => {
        println("<congruenceCall><from>" + id + "</from>\n<input>" + fx + "</input>")
        val mfy = r(fx)
        println("</congruenceCall>")
        mfy
      }

      Strategy.trace[M,F[A],F[B]](id)(self[F,M](rr)(F,M))(M)
    }
  }

  /*
   * Syntax
   */

  /** The [[zk.syntax.SearchOps]] corresponding to this congruence */
  final lazy val toSearchOps = new SearchOps[({type λ[β] = Congruence[X,Y,A,β]})#λ, B](this)(congruenceTrdInstances[X,Y,A])

  /** The [[zk.syntax.StrategyCategoryOps]] corresponding to this congruence */
  final lazy val toStrategyCategoryOps = new StrategyCategoryOps[({type λ[α,β] = Congruence[X,Y,α,β]})#λ, A ,B](this)(congruenceSndInstances[X,Y])

  /** The [[zk.syntax.CongruenceComposeOps]] corresponding to this congruence */
  final lazy val toCongruenceComposeOps = new CongruenceComposeOps[Congruence,X,Y,A,B](this)(congruenceInstances)
}


object Congruence {
  /** Lazy definition of a congruence. Useful when strict evaluation would not terminate. */
  def lazyDef[X,Y,A,B](s: => Congruence[X,Y,A,B]): Congruence[X,Y,A,B] = new Congruence[X,Y,A,B] {
    lazy val strat : Congruence[X,Y,A,B] = s

    def apply[F[_], M[_]](r: F[X] => M[F[Y]])(implicit F: Esrevart[F], M : MonadSearch[M]): F[A] => M[F[B]] =
      (fa:F[A]) => strat[F,M](r)(F,M)(fa)
  }

  /*
   * Lifting
   */

  /** Maps an [[ELens]] to a [[Congruence]]. */
  def map[N[_],A,X,Y,B](f: ELens[N,A,X,Y,B])(implicit N : MonadSearchInjection[N]) : Congruence[X,Y,A,B] = new Congruence[X,Y,A,B] {
    def apply[F[_], M[_]](r: F[X] => M[F[Y]])(implicit F: Esrevart[F], M : MonadSearch[M]): F[A] => M[F[B]] = {

      val nat : NaturalTransformation[N,M] = N.monadSearchInject[M](M)

      val ff : ELens[M,F[A],F[X],F[Y],F[B]] =
        F.liftELens[M,A,X,Y,B](ELens[M,A,X,Y,B](
            (a:A) => Rotareti.transform[N,M,X,Y,B](f.lens(a) , nat)(N,M)
          , (x:X) => nat[Y](f.default(x)))
        )

      (fa: F[A]) => M.bind(ff.lens(fa))(_.getAnswer(r))
    }
  }

  /** Maps an [[ELens]] on [[AnyMonadSearch]] to a [[Congruence]]  */
  def mapfs[A,X,Y,B](f : ELens[AnyMonadSearch,A,X,Y,B]) : Congruence[X,Y,A,B] = map[AnyMonadSearch,A,X,Y,B](f)(anyMonadSearch)

  /** Maps an [[ELens]] on Id to a [[Congruence]]  */
  def mapId[A,X,Y,B](f : ELens[Id        ,A,X,Y,B]) : Congruence[X,Y,A,B] = map[Id        ,A,X,Y,B](f)(idInstances)

  /** The main mapping function.
   *
   * @param f the function to map to a [[Congruence]]
   * @param default the [[Strategy]] to apply on ''X'' if ''F[X]'' is not possible to get.
   */
  def mapcm[A,X,Y,B](f : A => CongruenceMonad[X,Y,B,B])(implicit default : Strategy[X,Y]) : Congruence[X,Y,A,B] =
    new Congruence[X,Y,A,B] {
      def apply[F[_], M[_]](r: F[X] => M[F[Y]])(implicit F: Esrevart[F], M : MonadSearch[M]): F[A] => M[F[B]] = (fa:F[A]) => {

        val f2 : A => M[Rotareti[M,X,Y,B]] = (a:A) =>
          try Rotareti.transform[AnyMonadSearch,M,X,Y,B]( f(a)((b:B) => anyMonadSearch.point(Answer[AnyMonadSearch,X,Y,B](b)))
                                                    , anyMonadSearch.monadSearchInject[M](M)
                                                    )
          catch { case e : MatchError => M.empty[Rotareti[M,X,Y,B]] }


        val mfr : M[F[Rotareti[M,X,Y,B]]] = F.traverse[M,A, Rotareti[M,X,Y,B]](fa)(f2)(M)
        val mrf : M[Rotareti[M,F[X],F[Y],F[B]]] = M.bind(mfr)(F.esrevart[M,X,Y,B](default[M](M))(M))

        M.bind(mrf)(_.getAnswer(r))
      }
    }

  /** Equivalent to [[mapcm]] with X = Y (i.e. on Endomorphisms). */
  def mapcme[A,X,B](f : A => CongruenceMonad[X,X,B,B]) : Congruence[X,X,A,B] =
    mapcm[A,X,X,B](f)(Strategy.id[X])


  /** Equivalent to [[mapcm]] with one single hole (i.e. [[Context]]) */
  def mapCtx[A,X,Y,B](f: A => Context[X, Y, B])        : Congruence[X,Y,A,B] =
    mapfs[A,X,Y,B]( ELens[AnyMonadSearch,A,X,Y,B]( (a : A) => anyMonadSearch.point(f(a).toRotareti[AnyMonadSearch](anyMonadSearch))
                                             , Strategy.fail[X,Y][AnyMonadSearch](anyMonadSearch))
                  )

  /** The simplest of all mappings: maps any function to a [[Congruence]]. The resulting congruence ignore its input.
    * It returns a lifted form of ''f''.
    */
  def mapCst[X,Y,A,B](f: A => B) : Congruence[X,Y,A,B] =
    mapfs[A,X,Y,B](ELens[AnyMonadSearch,A,X,Y,B]( (a : A) => anyMonadSearch.point(Answer[AnyMonadSearch,X,Y,B](f(a)))
                                            , Strategy.fail[X,Y][AnyMonadSearch](anyMonadSearch))
                  )


  /** Given a [[Strategy]] from A to B as default case, returns the Congruence corresponding to a Traverse. */
  implicit def traverseToCongruence[G[_],A,B](atob : Strategy[A,B])(implicit G: Traverse[G]): Congruence[A,B,G[A],G[B]] =
    mapcm[G[A],A,B,G[B]]((ga:G[A]) => G.traverse[({type λ[α] = CongruenceMonad[A,B,G[B],α]})#λ, A, B](ga)(rewrite[A,B,G[B]] _)(congruenceMonad[A,B,G[B]]))(atob)

  /** Given a [[Strategy]] from A to B as default case, returns the Congruence corresponding to an [[EsrevartAble]]. */
  implicit def esrevartAbleToCongruence[GD[_], GC[_], A, B](atob : Strategy[A,B])(implicit G: EsrevartAble[GD,GC]): Congruence[A ,B, GD[A], GC[B]] = new Congruence[A ,B, GD[A], GC[B]] {
    def apply[F[_], M[_]](r: F[A] => M[F[B]])(implicit F: Esrevart[F], M : MonadSearch[M]): F[GD[A]] => M[F[GC[B]]] = {
      val rG : EsrevartReductible[F,GD,GC] = G[F]

      type TM[X] = rG.T[M,X]
      implicit val TM : MonadSearch[TM] = rG.T[M](M)

      val rT : F[A] => TM[F[B]] = (fa:F[A]) => rG.T.liftM[M,F[B]](r(fa))(M)

      val cZ : Congruence[A, B, rG.Z[A], rG.Z[B]] = traverseToCongruence[rG.Z,A,B](atob)(rG.Z)

      rG[M,A,B].from(cZ[F,TM](rT)(F,TM))
    }
  }



  /*
   * Library
   */


  /** A constant [[Congruence]]. */
  def cst[X,Y,A,B](pr: Strategy[A,B]): Congruence[X,Y,A,B] = new Congruence[X,Y,A, B] {
    def apply[F[_], M[_]](r: F[X] => M[F[Y]])(implicit F: Esrevart[F], M:MonadSearch[M]): F[A] => M[F[B]] = pr.liftTraverse[F](F)[M](M)
  }


  /** Congruence for the first component of a pair. */
  def first[A,B,C]  : Congruence[A,B,(A,C),(B,C)] = Congruence.mapCtx((p:(A,C)) => Context(p._1 , (b:B) => (b,p._2)))

  /** Congruence for the second component of a pair. */
  def second[A,B,C] : Congruence[A,B,(C,A),(C,B)] = Congruence.mapCtx((p:(C,A)) => Context(p._2 , (b:B) => (p._1,b)))


  /** Given a [[Strategy]] from A to B as default case, returns a [[Congruence]] for streams */
  def traverseStream[A, B](ab : Strategy[A,B]) : Congruence[A, B, Stream[A] , Stream[B]] = traverseToCongruence[Stream, A, B](ab)(std.Implicits.streamInstances)

  /** The identity [[Congruence]] */
  def idC[X,Y] = congruenceInstances.id[X,Y]

  def cstId[X,Y,A]: Congruence[X,Y,A,A] = cst[X,Y,A,A](Strategy.id[A])

  /** Tries its input, fallback on id on failure. */
  def stry[X]: Congruence[X,X,X,X] = idC[X,X] || cstId[X, X, X]

  /** Repeats its input until failure. Returns last successful result */
  def repeat[X]: Congruence[X,X,X,X] = new Congruence[X,X,X,X] {
    def apply[F[_], M[_]](r: (F[X]) => M[F[X]])(implicit F: Esrevart[F], M: MonadSearch[M]): (F[X]) => M[F[X]] = {

      def aux(fx: F[X]) : M[F[X]] = {
        val mt : M[F[X] \/ F[X]] = M.mtry[F[X]\/F[X]](M.apply(r(fx))(\/.left(_)), M.point(\/.right(fx)))
        M.bind[F[X] \/ F[X],F[X]](mt)((x: F[X] \/ F[X]) => x match {
          case -\/(fxr) => aux(fxr)
          case\/-(fxr)  => M.point[F[X]](fxr)
        })
      }

      aux _
    }
  }

  /** Compute the fixed point of its input */
  def fix[X,Y,A,B](f: (Congruence[X,Y,A,B]) => Congruence[X,Y,A,B]): Congruence[X,Y,A,B] = new Congruence[X,Y,A,B] { self =>
    lazy val me = f(self)

    def apply[F[_], M[_]](r: F[X] => M[F[Y]])(implicit F: Esrevart[F], M :  MonadSearch[M]): F[A] => M[F[B]] = me[F, M](r)(F,M)
  }

  /** Fail on its input's fixed points */
  def noId[A] : Congruence[A,A,A,A] = new Congruence[A,A,A,A] {
    def apply[F[_], M[_]](r: (F[A]) => M[F[A]])(implicit F: Esrevart[F], M: MonadSearch[M]): (F[A]) => M[F[A]] =
      (fa:F[A]) => M.bind[F[A],F[A]](r(fa))((fa2:F[A]) => if (fa == fa2) M.empty[F[A]] else M.point[F[A]](fa2))
  }



 /*
  * INSTANCES
  */

  /** Instances satisfied by Congruence */
  trait CongruenceInstances extends CongruenceCompose[Congruence] {
    final def id[X,Y] : Congruence[X, Y, X, Y] = new Congruence[X, Y, X, Y] {
      def apply[F[_], M[_]](r: F[X] => M[F[Y]])(implicit F: Esrevart[F], M:MonadSearch[M]): F[X] => M[F[Y]] = r
    }

    final def lConCompose[X,Y,A,B,R,S](s2: => Congruence[A, B, R, S], s1: => Congruence[X, Y, A, B]): Congruence[X, Y, R, S] =
      new Congruence[X, Y, R, S] {
        lazy val ls1: Congruence[X, Y, A, B] = s1
        lazy val ls2: Congruence[A, B, R, S] = s2

        def apply[F[_], M[_]](r: F[X] => M[F[Y]])(implicit F: Esrevart[F], M:MonadSearch[M]): F[R] => M[F[S]] = {
          lazy val strat : F[A] => M[F[B]] = ls1[F,M](r)(F,M)
          ls2[F,M]((fa:F[A]) => strat(fa))(F,M)
        }
      }

    final def  conFirst[X,Y,A,B,R,S](c : Congruence[X, Y, A, B])(implicit rs : StrategyRel[R,S]) : Congruence[(X,R),(Y,S),(A,R),(B,S)] =
      c.esrevartAble[({type λ[α] = (α, R)})#λ, ({type λ[α] = (α, S)})#λ](EsrevartAble.first[R,S](rs))

    final def conSecond[X,Y,A,B,R,S](c : Congruence[X, Y, A, B])(implicit rs : StrategyRel[R,S]) : Congruence[(R,X),(S,Y),(R,A),(S,B)] =
      c.esrevartAble[({type λ[α] = (R, α)})#λ, ({type λ[α] = (S, α)})#λ](EsrevartAble.second[R,S](rs))
  }


  /** Instances satisfied by Congruence[X,Y,_,_] for some X and Y */
  trait CongruenceSndInstances[X,Y] extends StrategyCategory[({type λ[α,β] = Congruence[X,Y,α,β]})#λ] {
    final def id[A]: Congruence[X, Y, A, A] = new Congruence[X, Y, A, A] {
      def apply[F[_], M[_]](r: F[X] => M[F[Y]])(implicit F: Esrevart[F], M:MonadSearch[M]): F[A] => M[F[A]] = (fa:F[A]) => M.point[F[A]](fa)
    }

    final def arr[A,B](f : A => B) : Congruence[X,Y,A,B] = new Congruence[X, Y, A, B] {
      def apply[F[_], M[_]](r: F[X] => M[F[Y]])(implicit F: Esrevart[F], M:MonadSearch[M]): F[A] => M[F[B]] = (fa:F[A]) => M.point[F[B]](F.map(fa)(f))
    }

    final def lcompose[A, B, C](s2: => Congruence[X, Y, B, C], s1: => Congruence[X, Y, A, B]): Congruence[X, Y, A, C] =
      new Congruence[X, Y, A, C] {
        lazy val ls1: Congruence[X, Y, A, B] = s1
        lazy val ls2: Congruence[X, Y, B, C] = s2

        def apply[F[_], M[_]](r: F[X] => M[F[Y]])(implicit F: Esrevart[F], M:MonadSearch[M]): F[A] => M[F[C]] =
          kleisliCompose[M,F[A],F[B],F[C]](ls2[F,M](r)(F,M), ls1[F,M](r)(F,M))(M)
      }


    final def first[A, B, C](c  : Congruence[X, Y, A, B]) : Congruence[X, Y, (A, C), (B, C)] = congruenceInstances.lConCompose(Congruence.first[A,B,C]  , c)
    final override def second[A, B, C](c : Congruence[X, Y, A, B]) : Congruence[X, Y, (C, A), (C, B)] = congruenceInstances.lConCompose(Congruence.second[A,B,C] , c)
  }





  /** Instances satisfied by Congruence[X,Y,A,_] for some X, Y and A */
  trait CongruenceTrdInstances[X,Y,A] extends Search[({type λ[β] = Congruence[X,Y,A,β]})#λ] {

    final def empty[B]: Congruence[X,Y,A,B] = Congruence.cst[X,Y,A,B](strategySndInstances[A].empty[B])

    final def plus[B](sa: Congruence[X,Y,A,B], sb: => Congruence[X,Y,A,B]): Congruence[X,Y,A, B] = new Congruence[X,Y,A, B] {
      def apply[F[_], M[_]](r: F[X] => M[F[Y]])(implicit F: Esrevart[F], M:MonadSearch[M]): F[A] => M[F[B]] = (fa:F[A]) => M.plus(sa[F, M](r)(F,M)(fa) , sb[F, M](r)(F,M)(fa))
    }

    final def local[B](sa: Congruence[X,Y,A, B]): Congruence[X,Y,A, B] = new Congruence[X,Y,A, B] {
      def apply[F[_], M[_]](r: F[X] => M[F[Y]])(implicit F: Esrevart[F], M:MonadSearch[M]): F[A] => M[F[B]] = (fa:F[A]) => M.local(sa[F, M](r)(F,M)(fa))
    }

    final def mtry[B](sa: Congruence[X,Y,A, B], sb: => Congruence[X,Y,A, B]): Congruence[X,Y,A, B] = new Congruence[X,Y,A, B] {
      def apply[F[_], M[_]](r: F[X] => M[F[Y]])(implicit F: Esrevart[F], M:MonadSearch[M]): F[A] => M[F[B]] = (fa:F[A]) => M.mtry(sa[F, M](r)(F,M)(fa) , sb[F, M](r)(F,M)(fa))
    }

    final def ~*[B, C](sa: Congruence[X,Y,A,B], sb: => Congruence[X,Y,A,C]): Congruence[X,Y,A,(B,C)] = new Congruence[X,Y,A, (B,C)] {
      def apply[F[_], M[_]](r: F[X] => M[F[Y]])(implicit F: Esrevart[F], M:MonadSearch[M]): F[A] => M[F[(B,C)]] = (fa:F[A]) => M.apply(M.~*(sa[F, M](r)(F,M)(fa) , sb[F, M](r)(F,M)(fa)))((p : (F[B],F[C])) => F.zip[B,C](p._1,p._2))
    }

    final def *~[B, C](sa: Congruence[X,Y ,A,B], sb: => Congruence[X,Y,A,C]): Congruence[X,Y,A,(B,C)] = new Congruence[X,Y,A, (B,C)] {
      def apply[F[_], M[_]](r: F[X] => M[F[Y]])(implicit F: Esrevart[F], M:MonadSearch[M]): F[A] => M[F[(B,C)]] = (fa:F[A]) => M.apply(M.*~(sa[F, M](r)(F,M)(fa) , sb[F, M](r)(F,M)(fa)))((p : (F[B],F[C])) => F.zip[B,C](p._1,p._2))
    }
  }


}


