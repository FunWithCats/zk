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

  import scalaz.{Equal, PlusEmpty}
  import syntax._


  /** scalaz.PlusEmpty extended with backtracking.
    *
    * Provides operations on a functor ''F'':
    * - an empty instance of ''F[A]'' for any type ''A''.
    * - plus: merge two instances.
    * - mtry: Try/Catch mechanism.
    * - local: bound backtracking.
    */

  trait Search[F[_]] extends PlusEmpty[F] {
    /** Try/Catch operator.
      *
      * @param fa computation to test for emptyness.
      * @param fb computation to return in case of fa being empty.
      * @tparam A type of the computation.
      * @return   ''fa'' if it is not empty, ''fb'' otherwise.
      */
    def mtry[A](fa: F[A], fb: => F[A]): F[A]

    /** Prevents backtracking from escaping outside of ''fa'' */
    def local[A](fa: F[A]): F[A]

    /** Product: left-hand side effects run first. */
    def ~*[A, B](ma: F[A], mb: => F[B]): F[(A, B)]

    /** Product: right-hand side effetcs run first. */
    def *~[A, B](ma: F[A], mb: => F[B]): F[(A, B)]


    trait SearchLaw {
      /** mtry associativity: mtry(mtry(X , Y), Z) = mtry(X, mtry(Y, Z)) */
      def mtryAssociative[A](fa : F[A], fb : F[A], fc : F[A])(implicit FA:Equal[F[A]]) : Boolean = FA.equal(mtry[A](mtry[A](fa,fb), fc) , mtry[A](fa, mtry[A](fb,fc)))

      /** mtry failure law */
      def mtryFailure[A](fa:F[A])(implicit FA:Equal[F[A]]) : Boolean = FA.equal(mtry[A](empty[A], fa) , fa)
    }

    def searchLaw = new SearchLaw { }

    /** syntax object associated to this. */
    object searchSyntax extends SearchSyntax[F] {
      final val F: Search[F] = Search.this
    }
  }

  object Search {
    /** returns the implicit [[Search]] instance of ''F''. */
    def apply[F[_]](implicit F: Search[F]): Search[F] = F
  }
}


package zk.syntax {

  import zk._
  import scalaz.syntax.{Ops, PlusEmptySyntax}

/** Wraps a value ''self'' and provides methods related to [[Search]].  */
  final case class SearchOps[F[_], A](val self: F[A])(implicit F: Search[F]) extends Ops[F[A]] {
    def local: F[A] = F.local[A](self)

    def mtry(fb: => F[A]): F[A] = F.mtry[A](self, fb)

    def ~*[B](mb: => F[B]): F[(A, B)] = F.~*[A, B](self, mb)

    def *~[B](mb: => F[B]): F[(A, B)] = F.*~[A, B](self, mb)

    /** self + mb = F.plus(ma, mb) */
    def +(mb: => F[A]): F[A] = F.plus[A](self, mb)

    /** alias for ''mtry'' */
    def ||(mb: => F[A]): F[A] = F.mtry[A](self, mb)
  }

  trait ToSearchOps {
    final implicit def ToSearchOps[F[_], A](v: F[A])(implicit F: Search[F]) = new SearchOps[F, A](v)(F)
  }

  trait SearchSyntax[F[_]] extends PlusEmptySyntax[F] {
    def F: Search[F]

    final implicit def ToSearchOps[A](v: F[A]): SearchOps[F, A] = new SearchOps[F, A](v)(SearchSyntax.this.F)
  }
}



