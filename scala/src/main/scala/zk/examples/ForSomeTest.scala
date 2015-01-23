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
import scala.collection.immutable.TreeMap

object ForSomeTest {


  def fail[A] : EndoStrategy[A] = Strategy.fail[A,A].trace("fail")
  def titi2tata : EndoStrategy[String] = Strategy.map[String,String] { case "Titi" => "Tata" }


  /*
   * Lists
   */

  import Visitable._
  implicit val VisitList: EndoVisitable[List[String], String, Int] = listInstances1[String]

  val forList: EndoCongruence[String, List[String]] = forSome1[List[String], String, String, List[String], Int](VisitList).trace("forList")

  /*
   * Trees
   */
  type Env = TreeMap[String,String]

  implicit val VisitEnv: EndoVisitable[Env, (String,String) , String] = treeMapInstances1[String, String](Ordering.String)
  val forEnv: EndoCongruence[(String,String), Env] = forSome1[Env, (String,String), (String,String) , Env, String](VisitEnv).trace("forEnv")





  def showresult(name : String , x : => Any) {
    println("<" + name + ">")
    println("<result>" + x + "</result>")
    println("</" + name + ">")
  }

  type LogOption[A] = LogT[Option,A]
  implicit val logOption : MonadSearch[LogOption] = logTInstances[Option](optionInstances)

  type CodLogOption[A] = CodT[LogOption,A]
  implicit val codLogOption : MonadSearch[CodLogOption] = codTInstances[LogOption](logOption)


  val exList1 = List("Toto","Titi")
  val exEnv1 = TreeMap.empty[String,String] + (("a", "Toto")) + (("b", "Titi"))

  def run = {
    println("<ForSomeTest>")
    showresult("ListFail" , forList(fail[String])[CodLogOption](codLogOption)(exList1).run.run)
    showresult("ListOne"  , forList(titi2tata)[CodLogOption](codLogOption)(exList1).run.run)
    showresult("EnvFail"  , forEnv(fail[(String,String)])[CodLogOption](codLogOption)(exEnv1).run.run)
    showresult("EnvOne"   , forEnv(Strategy.id[String] ~** titi2tata)[CodLogOption](codLogOption)(exEnv1).run.run)
    println("</ForSomeTest>")
  }
}
