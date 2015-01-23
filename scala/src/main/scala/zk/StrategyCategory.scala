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

  import scalaz._

  trait StrategyCategory[=>:[_, _]] extends Arrow[=>:] {
    import syntax._

    def lcompose[A, B, C](f: => (B =>: C), g: => (A =>: B)): A =>: C

    final def andThen[A, B, C](f: => (A =>: B), g: => (B =>: C)): A =>: C = lcompose[A, B, C](g, f)

    final def compose[A, B, C](f: (B =>: C), g: (A =>: B)): A =>: C = lcompose[A, B, C](f, g)

    object strategyCategorySyntax extends StrategyCategorySyntax[=>:] {
      final val F = StrategyCategory.this
    }
  }

  object StrategyCategory {
    def apply[=>:[_, _]](implicit F: StrategyCategory[=>:]): StrategyCategory[=>:] = F
  }
}

package zk.syntax {

  import zk._
  import scalaz.syntax.{Ops, CategorySyntax}

  final case class StrategyCategoryOps[=>:[_, _], A, B](val self: A =>: B)(implicit val F: StrategyCategory[=>:]) extends Ops[=>:[A, B]] {
    def lcompose[C](g: => (C =>: A)): C =>: B = F.lcompose[C, A, B](self, g)

    def <=<[C](g: => (C =>: A)): C =>: B = F.lcompose[C, A, B](self, g)

    def andThen[C](g: => (=>:[B, C])): A =>: C = F.lcompose[A, B, C](g, self)

    def >=>[C](g: => (B =>: C)): A =>: C = F.lcompose[A, B, C](g, self)

    def compose[C](g: (C =>: A)): C =>: B = F.lcompose[C, A, B](self, g)

    def ~**[C, D](other: => (C =>: D)): (A, C) =>: (B, D) = F.lcompose(F.second[C, D, B](other), F.first[A, B, C](self))

    def **~[C, D](other: => (C =>: D)): (A, C) =>: (B, D) = F.lcompose(F.first[A, B, D](self), F.second[C, D, A](other))
  }

  trait ToStrategyCategoryOps {
    final implicit def ToStrategyCategoryOps[=>:[_, _], A, B](v: A =>: B)(implicit F: StrategyCategory[=>:]) = new StrategyCategoryOps[=>:, A, B](v)(F)
  }

  trait StrategyCategorySyntax[=>:[_, _]] extends CategorySyntax[=>:] {
    def F: StrategyCategory[=>:]

    final implicit def ToStrategyCategoryOps[A, B](v: A =>: B): StrategyCategoryOps[=>:, A, B] = new StrategyCategoryOps[=>:, A, B](v)(StrategyCategorySyntax.this.F)
  }
}

