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

import scala.language.existentials

import scalaz.{NaturalTransformation, Traverse}
import zk.std.Implicits._

/**
 * The initial object of the MonadSearch category (i.e. with
 * Search monads as objects and MonadSearch morphisms as arrows).
 * There is a unique MonadSearch morphism from it to any MonadSearch.
 *
 * @tparam A
 */
abstract class AnyMonadSearch[A] {
  /** Transforms this into M[A] for any MonadSearch M */
  def inject[M[_]](implicit M : MonadSearch[M]) : M[A]
}

object AnyMonadSearch {
  def point[A] : A => AnyMonadSearch[A] = (a:A) => anyMonadSearch.point[A](a)
}

/** Instances satisfied by AnyMonadSearch: MonadSearch and MonadSearchInjection. */
trait AnyMonadSearchInstances extends MonadSearch[AnyMonadSearch] with MonadSearchInjection[AnyMonadSearch] {
  final def point[A](a : => A) : AnyMonadSearch[A] = new AnyMonadSearch[A] {
    def inject[M[_]](implicit M : MonadSearch[M]) : M[A] = M.point[A](a)
  }

  final def bind[X,B](pfa : AnyMonadSearch[X])(pf : X => AnyMonadSearch[B]) : AnyMonadSearch[B] = new AnyMonadSearch[B] {
    def inject[M[_]](implicit M : MonadSearch[M]) : M[B] = M.bind[X,B](pfa.inject[M](M))((x:X) => pf(x).inject[M](M))
  }

  final def empty[A] : AnyMonadSearch[A] = new AnyMonadSearch[A] {
    def inject[M[_]](implicit M : MonadSearch[M]) : M[A] = M.empty[A]
  }

  final def plus[A](f1 : AnyMonadSearch[A], f2 : => AnyMonadSearch[A]) : AnyMonadSearch[A] = new AnyMonadSearch[A] {
    def inject[M[_]](implicit M : MonadSearch[M]) : M[A] = {
      lazy val lf2 : M[A] = f2.inject[M](M)
      M.plus[A](f1.inject[M](M) , lf2)
    }
  }

  final def local[A](fa : AnyMonadSearch[A]) : AnyMonadSearch[A] = new AnyMonadSearch[A] {
    def inject[M[_]](implicit M : MonadSearch[M]) : M[A] = M.local[A](fa.inject[M](M))
  }

  final def mtry[A](f1 : AnyMonadSearch[A], f2 : => AnyMonadSearch[A]) : AnyMonadSearch[A] = new AnyMonadSearch[A] {
    def inject[M[_]](implicit M : MonadSearch[M]) : M[A] = {
      lazy val lf2 : M[A] = f2.inject[M](M)
      M.mtry[A](f1.inject[M](M) , lf2)
    }
  }

  final def monadSearchInject[M[_]](implicit M : MonadSearch[M]) : NaturalTransformation[AnyMonadSearch,M] =
    new NaturalTransformation[AnyMonadSearch,M] { def apply[A](fa : AnyMonadSearch[A]) : M[A] = fa.inject[M](M) }
}


/** An equivalence relation between two types A and B.
 *
 * @param to   a morphism from A to AnyMonadSearch[B]
 * @param from a morphism from B to AnyMonadSearch[A]
 * @tparam A
 * @tparam B
 */
sealed case class AnyMonadSearchRel[A,B](val to : A => AnyMonadSearch[B], val from : B => AnyMonadSearch[A]) { self =>

  lazy val flip : AnyMonadSearchRel[B,A] = new AnyMonadSearchRel[B,A](from,to) { override lazy val flip : AnyMonadSearchRel[A,B] = self }

  final def lift[F[_]](implicit F:Traverse[F]) : AnyMonadSearchRel[F[A],F[B]] = {
    val t : F[A] => AnyMonadSearch[F[B]] = (fa:F[A]) => F.traverse[AnyMonadSearch,A,B](fa)(to)(anyMonadSearch)
    val f : F[B] => AnyMonadSearch[F[A]] = (fb:F[B]) => F.traverse[AnyMonadSearch,B,A](fb)(from)(anyMonadSearch)

    AnyMonadSearchRel[F[A],F[B]](t,f)
  }
}


