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

object Implicits {

  import Strategy._
  import Congruence._
  import syntax._

  /*
   * Instances
   */

  implicit object strategyInstances               extends StrategyInstances
  implicit def    strategySndInstances[B]       = new     StrategySndInstances[B] {}

  implicit object congruenceInstances             extends CongruenceInstances
  implicit def    congruenceSndInstances[X,Y]   = new     CongruenceSndInstances[X,Y] {}
  implicit def    congruenceTrdInstances[X,Y,A] = new     CongruenceTrdInstances[X,Y,A] {}

  /*
   * Congruence
   */

  implicit def congruenceToCongruenceComposeOps[X,Y,A,B](c : Congruence[X,Y,A,B]) : CongruenceComposeOps[Congruence,X,Y,A,B] = c.toCongruenceComposeOps

  /*
   * StrategyOps
   */

  implicit def strategyToStrategyCategoryOps[A,B](s : Strategy[A,B]) : StrategyCategoryOps[Strategy,A,B] = s.toStrategyCategoryOps
  implicit def congruenceToStrategyCategoryOps[X,Y,A,B](c : Congruence[X,Y,A,B]) : StrategyCategoryOps[({type λ[α,β] = Congruence[X,Y,α,β]})#λ, A ,B] = c.toStrategyCategoryOps

  /*
   * To SearchOps
   */

  implicit def strategyToSearchOps[A,B](r: Strategy[A,B]): SearchOps[({type λ[α] = Strategy[A,α]})#λ, B] = r.toSearchOps
  implicit def congruenceToSearchOps[X,Y,A,B](c: Congruence[X,Y,A,B]): SearchOps[({type λ[β] = Congruence[X,Y,A,β]})#λ, B] = c.toSearchOps
}
