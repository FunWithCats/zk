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

import scalaz.Traverse
import scalaz.Id._
import scalaz.Isomorphism._

import std.Implicits._


/** A strategy is from A to B is a Kleisli arrow A => M[B] for any MonadSearch M.
  *
  * @tparam A type of the Domain.
  * @tparam B type of thr Codomain.
  */
abstract class Strategy[A,B] {
  self =>

  import syntax._
  import Implicits._

  /*
   * Application
   */

  def apply[M[_]](implicit M: MonadSearch[M]): A => M[B]

  final def apply[M[_]](a: A)(implicit M: MonadSearch[M]): M[B] = apply[M](M)(a)

  final def =<<[M[_]](a: M[A])(implicit M: MonadSearch[M]): M[B] = M.bind[A, B](a)(apply[M](M))

  /** Transform the strategy into a Kleisli arrow using the AnyMonadSearch monad */
  final def free : A => AnyMonadSearch[B] = (a:A) => new AnyMonadSearch[B] {
    def inject[M[_]](implicit M:MonadSearch[M]) : M[B] = self[M](M)(a)
  }


  /*
   * Functors
   */

  final def liftTraverse[F[_]](implicit F: Traverse[F]): Strategy[F[A], F[B]] = new Strategy[F[A],F[B]] {
    implicit def apply[M[_]](implicit M: MonadSearch[M]): F[A] => M[F[B]] = (fa:F[A]) => F.traverse[M,A,B](fa)(self[M](M))
  }

  final def esrevartReductible[W[_],FD[_],FC[_]](implicit WF: EsrevartReductible[W,FD,FC]): Strategy[W[FD[A]], W[FC[B]]] =
    new Strategy[W[FD[A]], W[FC[B]]] {
      implicit def apply[M[_]](implicit M: MonadSearch[M]): W[FD[A]] => M[W[FC[B]]] = {
        type TM[X] = WF.T[M, X]
        val TM: MonadSearch[TM] = WF.T[M](M)

        type WZ[X] = W[WF.Z[X]]
        val WZ: Esrevart[WZ] = WF.W `compose` WF.Z


        val r: WZ[A] => TM[WZ[B]] = (wza: WZ[A]) => WF.T.liftM[M, WZ[B]](WZ.traverse[M, A, B](wza)(self[M](M))(M))(M)
        WF[M, A, B](M).from(r)
      }
    }

  final def esrevartAble[FD[_],FC[_]](implicit F: EsrevartAble[FD,FC]): Strategy[FD[A],FC[B]] =
    esrevartReductible[Id,FD,FC](F[Id](idInstances))


  /*
   * Tracing
   */

  def trace(name: String): Strategy[A,B] = new Strategy[A,B] {
    implicit def apply[M[_]](implicit M: MonadSearch[M]): A => M[B] = Strategy.trace[M,A,B](name)(self[M](M))(M)
  }

  /*
   * Search
   */

  final lazy val toSearchOps = new SearchOps[({type λ[α] = Strategy[A,α]})#λ,B](this)(strategySndInstances[A])
  final lazy val toStrategyCategoryOps = new StrategyCategoryOps[Strategy,A,B](this)(strategyInstances)
}

object Strategy {

  import Implicits._

  /** Enrich the input arrow with tracing capabilities */
  def trace[M[_],A,B](name : String)(f : A => M[B])(implicit M: MonadSearch[M]) : A => M[B] = (a:A) => {
    println("<"+name+" type=\"strategy\">\n<input>" + a + "</input>")
    val res : M[B] = M.mtry( M.bind(f(a))((b:B) => {println("<output>\n<strategy>" + name + "</strategy>\n<value>" + b + "</value>\n</output>") ; M.point(b) })
                           , { println("<failed><strategy>" + name + "</strategy>\n<input>" + a + "</input>\n</failed>") ; M.empty[B] } )
    println("</" + name +">")
    res
  }

  /** Lazy definition of a Strategy */
  def lazyDef[A,B](pr: => Strategy[A,B]): Strategy[A,B] = new Strategy[A,B] {
    lazy val me = pr

    def apply[M[_]](implicit M: MonadSearch[M]): A => M[B] = (a:A) => me.apply[M](a)(M)
  }

  /** The identity strategy. */
  def id[A] : Strategy[A,A] = strategyInstances.id[A]

  /** The constant strategy */
  def cst[A,B](b: B): Strategy[A,B] = new Strategy[A,B] {
    implicit def apply[M[_]](implicit M: MonadSearch[M]): A => M[B] = (a: A) => M.point[B](b)
  }


  /** Isomorphism between Strategy[A,B] and A => AnyMonadSearch[B] */
  def anyMonadSearchIso[A,B] : Strategy[A,B] <=> (A => AnyMonadSearch[B]) =
    new (Strategy[A,B] <=> (A => AnyMonadSearch[B])) {
      val to   : Strategy[A,B] => (A => AnyMonadSearch[B]) = (s : Strategy[A,B]) => s.free
      val from : (A => AnyMonadSearch[B]) => Strategy[A,B] = (f :  A => AnyMonadSearch[B]) => new Strategy[A,B] {
        def apply[M[_]](implicit M : MonadSearch[M]) : A => M[B] = (a:A) => f(a).inject[M](M)
      }
    }

  def map[A,B](f: A => B) : Strategy[A,B] = new Strategy[A,B] {
    def apply[M[_]](implicit M : MonadSearch[M]) : A => M[B] = (a:A) =>
      try {
        val b = f(a)
        M.point[B](b)
      }
      catch { case e : MatchError => M.empty[B] }
  }

  def mapfs[A,B](f: A => AnyMonadSearch[B]) : Strategy[A,B] = new Strategy[A,B] {
    def apply[M[_]](implicit M : MonadSearch[M]) : A => M[B] = (a:A) =>
      try f(a).inject[M](M)
      catch { case e : MatchError => M.empty[B] }
  }

  /** Isomorphism between Straetgy[_,_] relations and _ => AnyMonadSrach[_] relations */
  def freeRelIso[A,B] : StrategyRel[A,B] <=> AnyMonadSearchRel[A,B] = new (StrategyRel[A,B] <=> AnyMonadSearchRel[A,B]) {
    final val   to : StrategyRel[A,B] => AnyMonadSearchRel[A,B] = (m : StrategyRel[A,B]) => AnyMonadSearchRel[A,B]( m.to[AnyMonadSearch](anyMonadSearch), m.from[AnyMonadSearch](anyMonadSearch))
    final val from : AnyMonadSearchRel[A,B] => StrategyRel[A,B] = (f : AnyMonadSearchRel[A,B]) => StrategyRel( anyMonadSearchIso[A,B].from(f.to), anyMonadSearchIso[B,A].from(f.from))
  }


  /** The fail strategy. It fails on every input */
  def fail[A,B] : Strategy[A,B] = new Strategy[A,B]{
    def apply[M[_]](implicit M : MonadSearch[M]) : A => M[B] = (a:A) => M.empty[B]
  }


  /*
   * INSTANCES
   */

  /** Instances satisfies by Strategy[_,_] */
  trait StrategyInstances extends StrategyCategory[Strategy] {
    final def id[A]: Strategy[A,A] = new Strategy[A,A] {
      implicit def apply[M[_]](implicit M: MonadSearch[M]): A => M[A] = (a:A) => M.point[A](a)
    }

    final def arr[A,B](f : A => B) : Strategy[A,B] = new Strategy[A,B] {
      def apply[M[_]](implicit M: MonadSearch[M]): A => M[B] = (a:A) => M.point[B](f(a))
    }

    final def lcompose[A,B,C](r1: => Strategy[B,C], r2: => Strategy[A,B]): Strategy[A,C] = new Strategy[A,C] {
      final lazy val lr1 : Strategy[B,C] = r1
      final lazy val lr2 : Strategy[A,B] = r2

      implicit def apply[M[_]](implicit M: MonadSearch[M]): A => M[C] = (a:A) => M.bind[B,C](lr2[M](M)(a))((b:B) => lr1[M](M)(b))
    }

    final def first[A, B, C](s  : Strategy[A, B]) : Strategy[(A, C), (B, C)] = s.liftTraverse[({type λ[α] = (α,C)})#λ](firstInstances[C])
    final override def second[A, B, C](s : Strategy[A, B]) : Strategy[(C, A), (C, B)] = s.liftTraverse[({type λ[α] = (C,α)})#λ](secondInstances[C])
  }

  /** Instances satisfies by Strategy[A,_] */
  trait StrategySndInstances[A] extends Search[({type λ[α] = Strategy[A,α]})#λ] {
    final def empty[B]: Strategy[A,B] = new Strategy[A,B] {
      def apply[M[_]](implicit M: MonadSearch[M]): A => M[B] = (a:A) => M.empty[B]
    }

    final def plus[B](ra: Strategy[A,B], rb: => Strategy[A,B]): Strategy[A,B] = new Strategy[A,B] {
      final lazy val lrb = rb
      def apply[M[_]](implicit M: MonadSearch[M]): A => M[B] = {
        import M.searchSyntax._
        (a:A) => ra[M](M)(a) + lrb[M](M)(a)
      }
    }

    final def local[B](ra: Strategy[A,B]): Strategy[A,B] = new Strategy[A,B] {
      def apply[M[_]](implicit M: MonadSearch[M]): A => M[B] = {
        import M.searchSyntax._
        (a:A) => ra[M](M)(a).local
      }
    }

    final def mtry[B](ra: Strategy[A,B], rb: => Strategy[A,B]): Strategy[A,B] = new Strategy[A,B] {
      lazy val lrb = rb
      def apply[M[_]](implicit M: MonadSearch[M]): A => M[B] = {
        import M.searchSyntax._
        (a:A) => ra[M](M)(a) || lrb[M](M)(a)
      }
    }

    final def ~*[B, C](ra: Strategy[A,B], rb: => Strategy[A,C]): Strategy[A, (B, C)] = new Strategy[A , (B, C)] {
      final lazy val lrb = rb
      def apply[M[_]](implicit M: MonadSearch[M]): A => M[(B,C)] = {
        import M.searchSyntax._
        (a:A) => ra[M](M)(a) ~* lrb[M](M)(a)
      }
    }

    final def *~[B, C](ra: Strategy[A,B], rb: => Strategy[A,C]): Strategy[A, (B, C)] = new Strategy[A , (B, C)] {
      final lazy val lrb = rb
      def apply[M[_]](implicit M: MonadSearch[M]): A => M[(B,C)] = {
        import M.searchSyntax._
        (a:A) => ra[M](M)(a) *~ lrb[M](M)(a)
      }
    }
  }

}


/** Objects reductibles to an Esrevart. Look at apply for a more precise definition */
abstract class EsrevartReductible[W[_], FD[_], FC[_]](implicit val W : Esrevart[W]) { F =>
  type Z[_]
  implicit val Z: Esrevart[Z]

  type T[_[_], _]
  implicit val T: MonadTransSearch[T]

  /** The isomorphism, for any MonadSearch M, that defines an EsrevartReductible */
  def apply[M[_], A, B](implicit M: MonadSearch[M]): (W[FD[A]] => M[W[FC[B]]]) <=> (W[Z[A]] => T[M, W[Z[B]]])
}

/** Strategy Relations between two types A and B */
case class StrategyRel[A,B](val to : Strategy[A,B], val from : Strategy[B,A]) { self =>
  lazy val flip : StrategyRel[B,A] = new StrategyRel[B,A](from, to) { override lazy val flip : StrategyRel[A,B] = self }

  final def lift[F[_]](implicit F : Traverse[F]) : StrategyRel[F[A],F[B]] = StrategyRel[F[A],F[B]](to.liftTraverse[F](F), from.liftTraverse[F](F))
}

object StrategyRel {
  implicit def ofIso[A,B](I : A <=> B) : StrategyRel[A,B] = StrategyRel(Strategy.map(I.to), Strategy.map(I.from))

  implicit def fail[A,B] : StrategyRel[A,B] = StrategyRel[A,B](Strategy.fail[A,B], Strategy.fail[B,A])

  implicit def id[A] : StrategyRel[A,A] = {
    val s = Strategy.id[A]
    StrategyRel[A,A](s,s)
  }
}
