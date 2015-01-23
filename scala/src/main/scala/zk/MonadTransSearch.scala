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

import scalaz.Isomorphism._

/** A [[Search]] preserving Monad Transformer.
  *
  * Transforms any [[MonadSearch]] ''M'' into a [[MonadSearch]] ''F[M,_]''.
  */
trait MonadTransSearch[F[_[_],_]] { F =>
  import MonadTransSearch._

  /** Lift an instance of ''M[A]'' to ''F[M,A]''. */
  def liftM[M[_],A](fa : M[A])(implicit M : MonadSearch[M]) : F[M,A]

  /** Returns a [[MonadSearch]] instance for ''F[M,_]'' */
  implicit def apply[M[_]](implicit pM: MonadSearch[M]): MonadSearch[({type λ[α] = F[M, α]})#λ]

  /** Compose this with another transformer ''G''.
    *
    * @return a [[MonadTransSearch]] instance for the transformer F[(λα.G[_,α]),_]
    */
  def compose[G[_[_],_]](implicit pG : MonadTransSearch[G]) : MonadTransSearch[({type λ[α[_],β] = F[({type λ[β] = G[α,β]})#λ , β]})#λ] =
    new MonadTransSearchCompose[F,G] {
      final val F = MonadTransSearch.this
      final val G = pG
    }

  /** Transform this transformer by isomorphism.
    *
    * If ''F[M,A]'' and ''G[M,A]]'' are isomorphic for any [[MonadSearch]] ''M'' and any ''A''.
    * Then ''G'' is [[MonadSearch]] transformer.
    *
    * @return a [[MonadTransSearch]] instance for ''G''.
    */
  final def iso[G[_[_],_]](implicit pI : MonadTransIso[F,G]) : MonadTransSearch[G] =
    new MonadTransSearchIso[F, G] {
      final val F = MonadTransSearch.this
      final val I  = pI
    }
}

object MonadTransSearch {


  trait MonadTransSearchCompose[F[_[_], _], G[_[_], _]] extends MonadTransSearch[({type λ[α[_], β] = F[({type λ[β] = G[α, β]})#λ, β]})#λ] {
    implicit val F: MonadTransSearch[F]
    implicit val G: MonadTransSearch[G]

    type FG[M[_], A] = F[({type λ[α] = G[M, α]})#λ, A]

    final def liftM[M[_], A](ma: M[A])(implicit M: MonadSearch[M]): F[({type λ[α] = G[M, α]})#λ, A] =
      F.liftM[({type λ[α] = G[M, α]})#λ, A](G.liftM[M, A](ma)(M))(G[M](M))

    final implicit override def apply[M[_]](implicit M: MonadSearch[M]): MonadSearch[({type λ[β] = FG[M, β]})#λ] =
      F[({type λ[α] = G[M, α]})#λ](G[M](M))
  }

  trait MonadTransIso[F[_[_], _], G[_[_], _]] {
    self =>
    def iso[M[_], A]: F[M, A] <=> G[M, A]

    val flip: MonadTransIso[G, F] = new MonadTransIso[G, F] {
      def iso[M[_], A]: G[M, A] <=> F[M, A] = self.iso[M, A].flip

      override val flip = self
    }
  }

  trait MonadTransSearchIso[F[_[_], _], G[_[_], _]] extends MonadTransSearch[G] {
    G =>
    implicit val F: MonadTransSearch[F]
    implicit val I: MonadTransIso[F, G]

    final def liftM[M[_], A](a: M[A])(implicit M: MonadSearch[M]): G[M, A] =
      I.iso[M, A].to(F.liftM[M, A](a)(M))

    trait MonadTransSearchApply[M[_]] extends MonadSearch[({type λ[α] = G[M, α]})#λ] {
      implicit val M: MonadSearch[M]

      implicit final val FM = F[M](M)

      import FM.monadSyntax._

      final def point[A](a: => A): G[M, A] = I.iso[M, A].to(FM.point[A](a))

      final def bind[A, B](fa: G[M, A])(f: (A) => G[M, B]): G[M, B] =
        I.iso[M, B].to(I.iso[M, A].from(fa) >>= (I.iso[M, B].from `compose` f))


      final def empty[A]: G[M, A] = I.iso[M, A].to(FM.empty[A])

      final def plus[A](ma: G[M, A], mb: => G[M, A]): G[M, A] =
        I.iso[M, A].to(FM.plus[A](I.iso[M, A].from(ma), I.iso[M, A].from(mb)))

      final def local[A](ma: G[M, A]): G[M, A] =
        I.iso[M, A].to(FM.local[A](I.iso[M, A].from(ma)))

      final def mtry[A](mt: G[M, A], me: => G[M, A]): G[M, A] =
        I.iso[M, A].to(FM.mtry[A](I.iso[M, A].from(mt), I.iso[M, A].from(me)))

      final override def mif[A, B](cond: G[M, A], mt: => G[M, B], me: => G[M, B]): G[M, B] =
        I.iso[M, B].to(FM.mif[A, B](I.iso[M, A].from(cond), I.iso[M, B].from(mt), I.iso[M, B].from(me)))
    }

    final override implicit def apply[M[_]](implicit pM: MonadSearch[M]): MonadSearch[({type λ[α] = G[M, α]})#λ] =
      new MonadTransSearchApply[M] {
        val M = pM
      }
  }


  trait MonadTransSearchGlue[F[_[_], _]] extends MonadTransSearch[F] {
    F =>
    def bind[M[_], A, B](fa: F[M, A])(f: (A) => F[M, B])(implicit M: MonadSearch[M]): F[M, B]

    final def glue[M[_], A](a: M[F[M, A]])(implicit M: MonadSearch[M]): F[M, A] =
      F.bind[M, F[M, A], A](F.liftM[M, F[M, A]](a))((tma: F[M, A]) => tma)(M)

    trait MonadTransSearchApply[M[_]] extends MonadSearch[({type λ[α] = F[M, α]})#λ] {
      implicit val M: MonadSearch[M]

      final def g[A](a: M[F[M, A]]): F[M, A] = glue[M, A](a)(M)

      final def point[A](a: => A): F[M, A] = F.liftM[M, A](M.point[A](a))

      final def bind[A, B](fa: F[M, A])(f: (A) => F[M, B]): F[M, B] = F.bind[M, A, B](fa)(f)(M)

      final def empty[A]: F[M, A] = F.liftM[M, A](M.empty[A])

      final def plus[A](ma: F[M, A], mb: => F[M, A]): F[M, A] =
        g[A](M.plus[F[M, A]](M.point[F[M, A]](ma), M.point[F[M, A]](mb)))

      final def local[A](ma: F[M, A]): F[M, A] = g[A](M.local[F[M, A]](M.point[F[M, A]](ma)))

      final def mtry[A](mt: F[M, A], me: => F[M, A]): F[M, A] =
        g[A](M.mtry[F[M, A]](M.point[F[M, A]](mt), M.point[F[M, A]](me)))

      final override def mif[A, B](cond: F[M, A], mt: => F[M, B], me: => F[M, B]): F[M, B] =
        g[B](M.mif[F[M, A], F[M, B]](M.point[F[M, A]](cond), M.point[F[M, B]](mt), M.point[F[M, B]](me)))
    }

    final implicit def apply[M[_]](implicit pM: MonadSearch[M]): MonadSearch[({type λ[α] = F[M, α]})#λ] =
      new MonadTransSearchApply[M] {
        final val M = pM
      }
  }

}
