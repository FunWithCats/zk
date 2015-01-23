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

package zk.examples

import zk._
import zk.Implicits._
import zk.std._
import zk.std.Implicits._

object Program {

  abstract class Expr
  case object Nop                        extends Expr
  case class Print(msg: String)          extends Expr
  case class Seq(e1: Expr, e2: Expr)     extends Expr
  case class Send(chan: String, e: Expr) extends Expr
  case class Receive(chan: String)       extends Expr

  type Output = String

  /*
   * Reduction rules
   */

  import StrategyRel.id

  /* Printing rule */
  val print: EndoStrategy[(Expr, Output)] = Strategy.map[(Expr, Output),(Expr, Output)]({
    case (Print(msg), s) => (Nop, (s + " " + msg))
  })//.trace("print")

  /* Message Passing Rule */
  val message: EndoStrategy[(Expr, Expr)] = Strategy.map[(Expr, Expr),(Expr, Expr)]({
    case (Send(c1, e), Receive(c2)) if c1 == c2 => (Nop, e)
    case (Receive(c1), Send(c2, e)) if c1 == c2 => (e, Nop)
  })//.trace("message")

  /*
   * Expr traversal
   */

  val cmexpr = congruenceMonad[Expr,Expr,Expr]
  import cmexpr.monadSearchSyntax._

  val down: EndoCongruence[Expr, Expr] = Congruence.mapcme[Expr,Expr,Expr]({
    case Seq(e1, e2) => for (v1 <- rewriteEndo[Expr,Expr](e1);
                             v2 <- if (v1 == Nop)  rewriteEndo[Expr,Expr](e2)
                                   else            cmexpr.point[Expr](Seq(v1,e2))
                            ) yield v2
    case e1          => cmexpr.point[Expr](e1)
  })//.trace("down")

  val traverseExpr: EndoCongruence[Expr, Expr] = (down <==< traverseExpr) >=> Congruence.repeat[Expr]


  /*
   * List traversal
   */

  import Visitable._

  implicit object VisitList extends ListInstances1[Expr]

  /*
   * Assembling pieces
   */

  type Config[A] = (List[A], Output)
  implicit val Config: EsrevartAble[Config, Config] = StateEsrevartAble[List, Output, Output]

  /* Combining Reduction rules */

  val reduceConfig: EndoStrategy[Config[Expr]] =
    forSome1(VisitList).conFirst[Output,Output].apply(print)  + (forSome2(VisitList)(message) ~** Strategy.id[Output])

  val traverseConfig: EndoStrategy[Config[Expr]] = traverseExpr[Config,Config](reduceConfig)


  /*
   * Tests
   */


  def genExpr(h: String, n: Int): Expr = if (n <= 1) Print(h + "-1") else Seq(genExpr(h, n - 1), Print(h + "-" + n))

  def genConfig(n: Int): Config[Expr] = (for (i <- (1 to n).toList) yield genExpr("Program" + i, 5 + n - i), "")

  val e1: Config[Expr] = (List(genExpr("Program1", 10)), "")
  val e2: Config[Expr] = genConfig(50)


  def showresult(name : String , x : => Any) {
    System.out.println("<" + name + ">")
    System.out.println("<Expr>" + x.toString + "</Expr>")
    System.out.println("</" + name + ">")
  }

  def run = {
    System.out.println("<Program>")
    showresult("SingleThread", traverseConfig[SLCodOption](e1).run.run)
    showresult("ThreeThreads", traverseConfig[SLCodOption](e2).run.run)
    System.out.println("</Program>")
  }
}

