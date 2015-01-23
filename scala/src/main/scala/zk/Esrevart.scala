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

import scalaz.{ IdT => _ , _}
import scalaz.Isomorphism._
import zk.std._
import zk.std.Implicits._

/*
 * Esrevart
 */

/** Type class for functors able to lift an [[ELens]].
  *
  *
  * @tparam F
  */
trait Esrevart[F[_]] extends Traverse[F] with Apply[F] with Zip[F] { F =>
  import Esrevart._
  import syntax._

  /*
   * Functional Traverse returning ELens
   */

  def esrevart[M[_],X,Y,B](default: X => M[Y])(implicit M : MonadSearch[M]) : F[Rotareti[M,X,Y,B]] => M[Rotareti[M,F[X],F[Y],F[B]]] = {
    import M.monadSearchSyntax.{ F => _}

    def aux(fr: F[Rotareti[M, X, Y, B]]): M[Rotareti[M, F[X], F[Y], F[B]]] = {

      val nexts: M[F[Focus[M, X, Y, B]]] = F.traverse[M, Rotareti[M, X, Y, B], Focus[M, X, Y, B]](fr)((r: Rotareti[M, X, Y, B]) => r match {
        case n: Focus[M, X, Y, B] => M.point[Focus[M, X, Y, B]](n)
        case _ => M.empty[Focus[M, X, Y, B]]
      })(M)

      lazy val answers: M[F[B]] = F.traverse[M, Rotareti[M, X, Y, B], B](fr)(_.getAnswer(default))(M)

      val liftNext: F[Focus[M, X, Y, B]] => Rotareti[M, F[X], F[Y], F[B]] = (fc: F[Focus[M, X, Y, B]]) => {
        val contexts: F[Y => M[Rotareti[M, X, Y, B]]] = F.map(fc)(_.context)

        val fcontext: F[Y] => M[Rotareti[M, F[X], F[Y], F[B]]] = (fy: F[Y]) =>
          M.bind(inverseTraverse[F, M, Rotareti[M, X, Y, B]](zipAp(fy)(contexts))(F, M))(aux _)

        Focus[M, F[X], F[Y], F[B]](F.map(fc)(_.focus), fcontext)
      }

      M.mtry( M.apply[F[Focus[M, X, Y, B]], Rotareti[M, F[X], F[Y], F[B]]](nexts)(liftNext)
        , M.apply[F[B],Rotareti[M,F[X],F[Y],F[B]]](answers)(Answer[M,F[X],F[Y],F[B]](_))
      )
    }

    aux _
  }


  def liftELens[M[_], A, X, Y, B](f: ELens[M,A,X,Y,B])(implicit M: MonadSearch[M]): ELens[M,F[A],F[X],F[Y],F[B]] =
    ELens[M,F[A],F[X],F[Y],F[B]]( (fa:F[A]) => M.bind(F.traverse[M,A, Rotareti[M,X,Y,B]](fa)(f.lens)(M))(esrevart[M,X,Y,B](f.default)(M))
      , (fx:F[X]) => F.traverse[M,X,Y](fx)(f.default)(M)
    )


  /*
   * More ap
   */

  final def zipAp[A,B](fa : F[A])(f: =>F[A=>B]) : F[B] = map(zip[A,A=>B](fa,f))(eval[A,B] _)
  final def zipApF[A,B](f: F[A=>B]) : F[A] =>  F[B] = (fa : F[A]) => map(zip[A,A=>B](fa,f))(eval[A,B] _)

  final def zipTraverseF[G[_],A,B](f: F[A=>G[B]])(implicit G: Applicative[G]) : F[A] =>  G[F[B]] =
    (fa : F[A]) => traverse[G,(A , A=>G[B]),B](zip[A,A=>G[B]](fa,f))(eval[A,G[B]] _)

  def ap[A,B](fa : =>F[A])(f: =>F[A=>B]) : F[B] = zipAp[A,B](fa)(f)

  final def apFM[G[_],A,B](ff : F[A => G[B]])(implicit G : Applicative[G]) : F[A] => G[F[B]] = (fa : F[A]) =>
    traverse[G,G[B],B](ap[A, G[B]](fa)(ff))(Predef.identity[G[B]])(G)

  final def ap2F[A,B,C](f : A => B => C) : F[A] => F[B] => F[C] =
    (fa : F[A]) => (fb : F[B]) => apply2[A,B,C](fa,fb)(Function.uncurried[A,B,C](f))

  /*
   * Functional Traverse
   */

  final def traverseF[M[_], A, B](f: (A) => M[B])(implicit M: Applicative[M]) : F[A] => M[F[B]] = (fa : F[A]) => traverse[M,A,B](fa)(f)(M)

  final def traverse2F[M[_],A,B,C](f : A => B => M[C])(implicit M : Applicative[M]) : F[A] => F[B] => M[F[C]] = {
    val ft : F[(A,B)] => M[F[C]] = (fab : F[(A,B)]) => traverse[M,(A,B),C](fab)((p : (A,B)) => f(p._1)(p._2))
    (fa : F[A]) => (fb : F[B]) =>
      ft(apply2[A,B,(A,B)](fa, fb)((a:A, b:B) => (a,b)))
  }

  final def traverse2FRot[M[_],K,A,X,Y,B](f : K => A => M[Rotareti[M,X,Y,B]], default : X => M[Y])(implicit M : MonadSearch[M]) : F[K] => F[A] => M[Rotareti[M,F[X],F[Y],F[B]]] =
    (fk:F[K]) => (fa:F[A]) => {
      val zka: F[(K, A)] = zip(fk,fa)

      val fc : ((K, A)) => M[Rotareti[M, X, Y, B]] = (p:(K,A)) => f(p._1)(p._2)

      val mf : M[F[Rotareti[M, X, Y, B]]] = F.traverse[M,(K,A),Rotareti[M,X,Y,B]](zka)(fc)(M)

      val esv: F[Rotareti[M, X, Y, B]] => M[Rotareti[M, F[X], F[Y], F[B]]] = esrevart[M,X,Y,B](default)(M)

      M.bind(mf)(esv)
    }


  /*
   * EsrevartAble
   */

  object esrevartAble extends EsrevartAble[F,F] {
    def apply[W[_]](implicit W: Esrevart[W]): EsrevartReductible[W, F, F] = new EsrevartReductible[W, F, F] {
      type Z[A] = F[A]
      implicit final val Z: Esrevart[Z] = F

      type T[M[_], A] = IdT[M, A]
      implicit final val T: MonadTransSearch[T] = idTInstances

      def apply[M[_], A, B](implicit M: MonadSearch[M]): (W[F[A]] => M[W[F[B]]]) <=> (W[Z[A]] => T[M, W[Z[B]]]) =
        new ((W[F[A]] => M[W[F[B]]]) <=> (W[Z[A]] => T[M, W[Z[B]]])) {
          val to: (W[F[A]] => M[W[F[B]]]) => (W[Z[A]] => T[M, W[Z[B]]]) = (r: W[F[A]] => M[W[F[B]]]) => r
          val from: (W[Z[A]] => T[M, W[Z[B]]]) => (W[F[A]] => M[W[F[B]]]) = (r: W[Z[A]] => T[M, W[Z[B]]]) => r
        }
    }
  }

  /*
   * Composition
   */

  final def compose[G[_]](pG: Esrevart[G]): Esrevart[({type λ[α] = F[G[α]]})#λ] =
    new EsrevartCompose[F, G] {
      final val F = Esrevart.this
      final val G = pG
    }

  /*
   * Syntax
   */

  object traverseELensSyntax extends EsrevartSyntax[F] {
    final val F = Esrevart.this
  }

}

object Esrevart {
  def apply[F[_]](implicit F: Esrevart[F]): Esrevart[F] = F


  trait EsrevartCompose[F[_], G[_]] extends Esrevart[({type λ[α] = F[G[α]]})#λ] { C =>
    implicit val F: Esrevart[F]
    implicit val G: Esrevart[G]

    final def traverseImpl[M[_], A, B](fa: F[G[A]])(f: (A) => M[B])(implicit M: Applicative[M]): M[F[G[B]]] = F.traverseF[M,G[A],G[B]](G.traverseF[M,A,B](f)(M))(M)(fa)

    final def zip[A,B](fa : =>F[G[A]], fb : =>F[G[B]]) : F[G[(A,B)]] =
      F.map(F.zip(fa,fb))((p : (G[A],G[B])) => G.zip(p._1,p._2))


    override def esrevart[M[_],X,Y,B](default: X => M[Y])(implicit M : MonadSearch[M]) : F[G[Rotareti[M,X,Y,B]]] => M[Rotareti[M,F[G[X]],F[G[Y]],F[G[B]]]] =
      (fgr : F[G[Rotareti[M,X,Y,B]]]) => {
        val fmg : M[F[Rotareti[M,G[X],G[Y],G[B]]]] = F.traverse[M,G[Rotareti[M,X,Y,B]],Rotareti[M,G[X],G[Y],G[B]]](fgr)(G.esrevart[M,X,Y,B](default)(M))(M)
        M.bind(fmg)(F.esrevart[M,G[X],G[Y],G[B]](G.traverseF[M,X,Y](default)(M)))
      }

    override def liftELens[M[_],A,X,Y,B](l : ELens[M,A,X,Y,B])(implicit M : MonadSearch[M]) : ELens[M,F[G[A]], F[G[X]], F[G[Y]], F[G[B]]] =
      F.liftELens[M,G[A],G[X],G[Y],G[B]](G.liftELens[M,A,X,Y,B](l)(M))(M)
  }
}
}

package zk.syntax {

  import scalaz.Applicative
  import scalaz.syntax.{TraverseSyntax, Ops, ApplySyntax, ZipSyntax}
  import zk._

  final case class EsrevartOps[F[_], A](val self: F[A])(implicit F: Esrevart[F]) extends Ops[F[A]] {
    def traverse2F[M[_], B, C](f: A => B => M[C])(implicit M: Applicative[M]): F[B] => M[F[C]] =
      F.traverse2F[M, A, B, C](f)(M)(self)
  }

  trait ToEsrevartOps {
    final implicit def ToEsrevartOps[F[_], A](v: F[A])(implicit F: Esrevart[F]) = new EsrevartOps[F, A](v)(F)
  }

  trait EsrevartSyntax[F[_]] extends TraverseSyntax[F] with ApplySyntax[F] with ZipSyntax[F] {
    implicit val F: Esrevart[F]

    final implicit def ToEsrevartOps[A](v: F[A]): EsrevartOps[F, A] = new EsrevartOps[F, A](v)(EsrevartSyntax.this.F)
  }
}

