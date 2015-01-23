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

import scalaz._
import scalaz.Isomorphism._

package object zk {

  /*
   * Types
   */

  type EndoStrategy[A]      = Strategy[A,A]
  type EndoCongruence[X, A] = Congruence[X,X,A,A]
  type Endo2Congruence[A]   = Congruence[A,A,A,A]
  type EndoVisitable[A,X,K] = Visitable[A,X,X,A,K]

  /*
   * Useful
   */

  implicit def liftIso[F[_],A,B](I : A <=> B)(implicit F : Functor[F]) : F[A] <=> F[B] =
    new (F[A] <=> F[B]) {
      val to   : F[A] => F[B] = F.lift[A,B](I.to)
      val from : F[B] => F[A] = F.lift[B,A](I.from)
    }

  def eval[A,B](p : (A,A=>B)) : B = p._2(p._1)

  def swapPair[A,B] : ((A,B)) => (B,A) = (p : (A,B)) => (p._2,p._1)

  def inverseTraverse[F[_],G[_],A](fma : F[G[A]])(implicit F:Traverse[F], G : Applicative[G]) : G[F[A]] =
    F.traverse[G,G[A],A](fma)(Predef.identity[G[A]])(G)

  def kleisliCompose[M[_],A,B,C](k1 : => (B => M[C]), k2 : => (A => M[B]))(implicit M : Bind[M]) : A => M[C] = {
    lazy val lk1 = k1
    lazy val lk2 = k2
    (a:A) => M.bind[B,C](lk2(a))((b:B) => lk1(b))
  }
}
