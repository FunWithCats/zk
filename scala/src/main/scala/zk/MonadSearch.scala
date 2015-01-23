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

  import scalaz.{NaturalTransformation, Monad, MonadPlus}
  import scalaz.syntax.Ops

  /** A [[scalaz.Monad]] that is also a [[Search]].  */
  trait MonadSearch[F[_]] extends MonadPlus[F] with Search[F] {

    import monadPlusSyntax._
    import searchSyntax._
    import zk.syntax._

    /** If-Then-Else construct on ''F''.
      *
      * @param c condition.
      * @param t then branch.
      * @param e else branch.
      * @return ''t'' if ''c'' is empty, ''e'' otherwise.
      */
    def mif[A, B](c: F[A], t: => F[B], e: => F[B]): F[B] = {
      val sc: F[Either[A, F[B]]] = apply[A, Either[A, F[B]]](c)((a: A) => Left(a))

      val pass: Either[A, F[B]] => F[F[B]] = (either: Either[A, F[B]]) => either match {
        case Left(_) => empty[F[B]]
        case Right(m) => point[F[B]](m)
      }

      join(((sc || point[Either[A, F[B]]](Right(e))) >>= pass) || point[F[B]](t))
    }

    /** product: left-hand side effetcs first. */
    def ~*[A, B](ma: F[A], mb: => F[B]): F[(A, B)] = ma >>= ((a: A) => apply(mb)((b: B) => (a, b)))

    /** product: right-hand side effetcs first. */
    def *~[A, B](ma: F[A], mb: => F[B]): F[(A, B)] = mb >>= ((b: B) => apply(ma)((a: A) => (a, b)))

    /** syntax object of this. */
    object monadSearchSyntax extends MonadSearchSyntax[F] {
      final val F: MonadSearch[F] = MonadSearch.this
    }
  }


  /** Provides a natural transformation from ''F'' to ''M'' for any [[MonadSearch]] ''M''. */
  trait MonadSearchInjection[F[_]] extends Monad[F] {
    def monadSearchInject[M[_]](implicit M: MonadSearch[M]): NaturalTransformation[F, M]
  }

}

package zk.syntax {

  import zk._
  import scalaz.syntax._
  import scalaz.{NaturalTransformation, Monad}

  /** Wraps a value ''self'' and provides methods related to [[MonadSearch]].  */
  final class MonadSearchOps[F[_], A](val self: F[A])(implicit val F: MonadSearch[F]) extends Ops[F[A]] {
    def mif[B](t: => F[B], e: => F[B]): F[B] = F.mif[A, B](self, t, e)
  }

  trait ToMonadSearchOps extends ToMonadPlusOps {
    final implicit def ToMonadSearchOps[F[_], A](v: F[A])(implicit F: MonadSearch[F]) = new MonadSearchOps[F, A](v)(F)
  }

  trait MonadSearchSyntax[F[_]] extends MonadPlusSyntax[F] {
    def F: MonadSearch[F]

    final implicit def ToMonadSearchOps[A](v: F[A]): MonadSearchOps[F, A] = new MonadSearchOps[F, A](v)(MonadSearchSyntax.this.F)
  }

  object MonadSearch {
    /** returns the implicit [[MonadSearch]] instance of ''F''. */
    def apply[F[_]](implicit F: MonadSearch[F]): MonadSearch[F] = F
  }
}
