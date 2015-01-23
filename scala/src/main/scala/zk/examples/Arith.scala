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

import scalaz.Isomorphism._
import collection.immutable.TreeMap
import zk._
import zk.Implicits._
import zk.Congruence._
import zk.std._
import zk.std.Implicits._


object Arith {
  /*
   *
   *  Expr
   *
   *
   */

  /*
   * We define here arithmetic expressions made of
   * intergers ( I(.) ), additions ( P(.,.) ) and
   * products ( M(.,.) ).
   */
  abstract class Expr
  case class I(x: Int)             extends Expr
  case class P(e1: Expr, e2: Expr) extends Expr
  case class M(e1: Expr, e2: Expr) extends Expr


  /* An example of expression */
  val e1 = M(I(3), P(I(2), I(3)))

  /*
   * Here is a very simple rewrite rule to
   * compute a sum or a product. Note that
   * children of P and M have to be integers
   * for the rule to success.
   */

  val reduce: EndoStrategy[Expr] = Strategy.map[Expr,Expr]({
    case P(I(x), I(y)) => I(x + y)
    case M(I(x), I(y)) => I(x * y)
  })

  /* reduceT has the same semantics than reduce but has tracing capabilities */
  val reduceT = reduce.trace("reduce")

  /*
   * To evaluate a sum or a product we need to evaluate their
   * sub expressions. The following rule, when applied on a term
   * P(e1,e2) or M(e1,e2) set one traverseZipperAble on e1 and one on e2 so
   * that both can be reduced.
   */

  val cmexpr = congruenceMonad[(Expr,Expr),(Expr,Expr),Expr]
  import cmexpr.monadSyntax.{ F => _ }


  val down: EndoCongruence[Expr, Expr] = Congruence.mapcme[Expr, Expr, Expr]({
    case P(e1, e2) => for (v1 <- rewriteEndo[Expr, Expr](e1);
                           v2 <- rewriteEndo[Expr, Expr](e2)
                      ) yield P(v1,v2)
    case M(e1, e2) => for (v1 <- rewriteEndo[Expr, Expr](e1);
                           v2 <- rewriteEndo[Expr, Expr](e2)
                      ) yield M(v1,v2)
  })

  import StrategyRel.id

  /* One again, its tracing version */
  val downT = down.trace("down")

  /*
   * The following rule is the tricky part of this example.
   * It is essentially the innermost combinator. It captures a congruence ctx
   * from expressions to expression (i.e. of type Congruence[Expr,Expr]), apply
   * itself to the subterms of its input and finly apply ctx on the resulting term.
   * Thus performing a bottom-up congruence.
   *
   * Note that this congruence does not mention which congruence ctx is. Its input
   * must be an expression and nothing more.
   */

  val traverseExpr: EndoCongruence[Expr, Expr] = (stry[Expr] <==< down <==< traverseExpr) >=> repeat[Expr]
  /* To evaluate an expression, we want to sun innermost(reduceT).
   * To do so, we can simply sequence traverseExpr with reduceT.
   * traverseExpr will capture reduceT as the congruence ctx and apply it
   * in an innermost fashion.
   */
  val evalExpr: EndoStrategy[Expr] = traverseExpr(reduceT)

  /*
   *
   *  Env
   *
   *
   */


  /*
   * This part present an extension of the previous example.
   * We want to add variables to arithmetic expressions.
   * So we stat by adding the variable case to the syntax of expressions.
   *
   * We also add the construction S(x,i) to set the value of the variable x
   * to i.
   */

  case class V(x: String)         extends Expr
  case class S(x: String, i: Int) extends Expr

  /* An example of expression with variables */
  val e2 = M(I(3), P(V("x"), V("y")))

  /* An second example of expression with variables */
  val e3 = M(S("x", 3)
    , P(V("x"), V("y"))
  )

  val e4 = P(S("y", 7)
    , M(V("x"), V("y"))
  )


  /*
   * To evaluate expressions with variables we need to give values to them.
   * These values are stored into an environment ( Env ) which is a mapping
   * from variable names to integers. For example the mapping of the variable "x"
   * to the value 5 is EnvAssoc("x",5)
   */


  case class EnvAssoc(name: String, value: Int)

  type Env = TreeMap[String, Int]

  /* An example of environment that maps the variable x to 1 and
   * the variable y to 2.
   */
  val env = TreeMap.empty[String, Int] + (("x", 2)) + (("y", 3)) + (("z", 4))

  /*
   * The following code make the environment a visitable structure.
   * An environment is a map from strings to integers. The following function
   * coerce it to a list of EnvAssoc.
   */

  implicit val VisitEnv: EndoVisitable[Env, EnvAssoc, String] = {
    val iso = new ((String, Int) <=> EnvAssoc) {
      def to: ((String, Int)) => EnvAssoc = (p: (String, Int)) => EnvAssoc(p._1, p._2)
      def from: (EnvAssoc) => (String, Int) = (e: EnvAssoc) => (e.name, e.value)
    }

    treeMapInstances1[String, Int](Ordering.String).iso[EnvAssoc, EnvAssoc](iso, iso)
  }

  /*
   * We need to add a rule to replace a variable in an expression by
   * its value in the environment. That the job of the "variable" rule.
   * Note that for now the correct EnvAssoc(y,i) such that x == y is found
   * magically.
   */
  val variable: EndoStrategy[(Expr, EnvAssoc)] = Strategy.map[(Expr, EnvAssoc),(Expr, EnvAssoc)]({
    case (V(x), EnvAssoc(y, i)) if x == y => (I(i), EnvAssoc(y, i))
    case (S(x, i), EnvAssoc(y, _)) if x == y => (I(i), EnvAssoc(y, i))
  })

  /* One again its tracing version */
  val variableT = variable.trace("variable")


  import Visitable._

  /*
   * With the new syntax, the reduction rule is either reduceT or the variable rule.
   * Note that they do not have the same definition domain. The variable rule need
   * a mapping as input which reduceT does not require.
   *
   * To make them compatible, we extend reduceT to the domain Expr x EnvAssoc of pairs
   * of expressions and mappings.
   */
  val traverseEnv: EndoCongruence[EnvAssoc, Env] = forSome1[Env, EnvAssoc, EnvAssoc, Env, String](VisitEnv)

  val traverseExprEnv: EndoCongruence[(Expr, EnvAssoc),(Expr, Env)] = traverseExpr.trace("travExpr") ***~ traverseEnv.trace("travEnv")

  val reduceEnvAssoc: EndoStrategy[(Expr, EnvAssoc)] = (reduceT ~** Strategy.id[EnvAssoc]) + variableT

  /*
   * Here is the interesting part. We still want an innermost reduction but we need to carry the environment
   * to be able to apply the variable rule. The traverseExpr rule was made to accept only expressions as input,
   * and neither environmnents nor mappings.
   *
   * Actually traverseExpr can still be used. It will transparently carry the environment and give it
   * to the variable rule.
   */
  val evalExprEnv: EndoStrategy[(Expr, Env)] = traverseExprEnv(reduceEnvAssoc)


  /*
   * As we saw, very little code needed to be adapted. The traverseExpr is very generic and does not need
   * to be modified when the syntax changes.
   */


  /*
   *
   *  Concurrency
   *
   *
   */

  val traverseConcurent: EndoCongruence[(Expr, EnvAssoc),((Expr, Expr), Env)] = (traverseExpr ~** traverseExpr) ***~ traverseEnv

  val evalConcurrent: EndoStrategy[((Expr, Expr), Env)] = traverseConcurent(reduceEnvAssoc)


  /*
   * BackTracking
   *
   */


  val reduceBacktrackEnvAssoc: EndoStrategy[EnvAssoc] = Strategy.map[EnvAssoc, EnvAssoc]({
    case EnvAssoc(x, _) => EnvAssoc(x, 42)
  }).trace("reduceBacktrackEnvAssoc")

  val reduceBacktrackEnv: EndoStrategy[Env] = traverseEnv(reduceBacktrackEnvAssoc).trace("reduceBacktrackEnv")

  val reduceBacktrackTestEnv: EndoStrategy[Env] = Strategy.anyMonadSearchIso.from( (e: Env) => e.get("d") match {
    case Some(42) => anyMonadSearch.point[Env](e)
    case _        => anyMonadSearch.empty[Env]
  }).trace("reduceBacktrackTestEnv")

  val evalBackTrack: EndoStrategy[Env] = reduceBacktrackEnv >=> reduceBacktrackTestEnv
  val e5 = TreeMap.empty[String, Int] + (("a", 1)) + (("b", 2)) + (("c", 3)) + (("d", 4)) + (("e", 5)) + (("f", 6)) + (("g", 7))

  /*
   *
   *  Test
   *
   *
   */


  def showresult(name : String , x : => Any) {
    System.out.println("<" + name + ">")
    System.out.println("<Expr>" + x.toString + "</Expr>")
    System.out.println("</" + name + ">")
  }

  def run = {
    System.out.println("<Arith>")
    showresult("ArithNoVar"      , evalExpr[SLCodOption](e1).run)
    showresult("ArithVar"        , evalExprEnv[SLCodOption]((e2, env)).run)
    showresult("ArithVarSet"     , evalExprEnv[SLCodOption]((e3, env)).run)
    showresult("ArithConcurrent" , evalConcurrent[SLCodOption](((e3, e4), env)).run)
    showresult("BackTrackLocal"  , evalBackTrack[Option](e5))
    showresult("BackTrackGlobal" , evalBackTrack[SLCodOption](e5).run)
    System.out.println("</Arith>")
  }
}

