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

import scalaz.{Ordering => _, _}
import scalaz.Isomorphism._
import scalaz.Id._

import std._
import std.Implicits._

/** Types that can be wiewed as/converted into a Tree-like structure with K-indexed children.*/
trait Visitable[A, X, Y, B, K] {
  V =>

  import syntax._

  implicit val KeysOrdering: Ordering[K]

  /** Given an object of type A, returns the collection of the keys of its children. */
  def keys(a: A): Stream[K]

  /** The default strategy to apply when lifting fails */
  def default[F[_]](implicit F: Traverse[F]): Strategy[F[X], F[Y]]

  /** The lens to access/modify any combination of children at position F[K] in A */
  def lens[F[_], M[_]](implicit F: Traverse[F], M: MonadSearch[M]): F[K] => A => M[Rotareti[M, F[X], F[Y], B]]

  /** The lens on children */
  final def children[F[_], M[_]](lk: F[K])(implicit F: Traverse[F], M: MonadSearch[M]): ELens[M, A, F[X], F[Y], B] =
    ELens[M, A, F[X], F[Y], B](lens[F, M](F, M)(lk), default[F](F)[M](M))

  /** Focus on One child at position k */
  final def child1[M[_]](k: K)(implicit M: MonadSearch[M]): ELens[M, A, X, Y, B] = children[Id, M](k)(Id.id, M)

  /** Focus on two children at positions k1 and k2 */
  final def child2[M[_]](k1: K, k2: K)(implicit M: MonadSearch[M]): ELens[M, A, (X, X), (Y, Y), B] = children[Pair, M]((k1, k2))(pairInstances, M)

  /** Focus on every child */
  final def allChildren[M[_]](implicit M: MonadSearch[M]): ELens[M, A, Stream[X], Stream[Y], B] =
    ELens[M, A, Stream[X], Stream[Y], B]((a: A) => lens[Stream, M](streamInstances, M)(keys(a))(a), default[Stream](streamInstances)[M](M))

  /*
  def compose[R,S,L](next: Visitable[X, R, S, Y, L]): Visitable[A, R, S, B, (K, L)] =
    new VisitableCompose[A,X,R,S,Y,B,K,L] {
      val VL = V
      val VR = next
      val KeysOrdering: Ordering[(K, L)] = Ordering.Tuple2[K, L](V.KeysOrdering, next.KeysOrdering)
    }
*/

  /** Transforms this by isomorphism of its domain (X <=> R) and its codomain (Y <=> S) */
  final def iso[R, S](implicit domain: X <=> R, codomain: Y <=> S): Visitable[A, R, S, B, K] = new Visitable[A, R, S, B, K] {
    implicit val KeysOrdering: Ordering[K] = V.KeysOrdering

    def keys(a: A): Stream[K] = V.keys(a)

    def default[F[_]](implicit F: Traverse[F]): Strategy[F[R], F[S]] = {
      val sxy: Strategy[F[X], F[Y]] = V.default[F](F)
      val fdomain: F[X] <=> F[R] = liftIso[F, X, R](domain)(F)
      val fcodomain: F[Y] <=> F[S] = liftIso[F, Y, S](codomain)(F)

      new Strategy[F[R], F[S]] {
        def apply[M[_]](implicit M: MonadSearch[M]): F[R] => M[F[S]] = (fr: F[R]) => M.apply(sxy[M](M)(fdomain.from(fr)))(fcodomain.to)
      }
    }

    def lens[F[_], M[_]](implicit F: Traverse[F], M: MonadSearch[M]): F[K] => A => M[Rotareti[M, F[R], F[S], B]] = {
      val l = V.lens[F, M](F, M)
      val fdomain: F[X] => F[R] = liftIso[F, X, R](domain)(F).to
      val fcodomain: F[S] => F[Y] = liftIso[F, Y, S](codomain)(F).from

      (fk: F[K]) => (a: A) => M.apply(l(fk)(a))(_.refocus[F[R], F[S]](fdomain, (fs: F[S]) => M.point(fcodomain(fs))))
    }
  }

  object visitableSyntax extends VisitableSyntax[A, X, Y, B, K] {
    final val V = Visitable.this
  }

}


object Visitable {
  def apply[F[_]](implicit F: Search[F]): Search[F] = F
  import Implicits._

  /** The Congruence on children lk of a Visitable */
  def children[F[_], A, X, Y, B, K](lk: F[K])(implicit F: Traverse[F], V: Visitable[A, X, Y, B, K]): Congruence[F[X], F[Y], A, B] =
    Congruence.mapfs[A, F[X], F[Y], B](V.children[F, AnyMonadSearch](lk)(F, anyMonadSearch))

  /** The Congruence on child k of a Visitable */
  def child1[A, X, Y, B, K](k: K)(implicit V: Visitable[A, X, Y, B, K]): Congruence[X, Y, A, B] = children[Id, A, X, Y, B, K](k)(idInstances, V)

  /** The Congruence on children k1 and k2 of a Visitable */
  def child2[A, X, Y, B, K](k1: K, k2: K)(implicit V: Visitable[A, X, Y, B, K]): Congruence[(X, X), (Y, Y), A, B] = children[Pair, A, X, Y, B, K]((k1, k2))(pairInstances, V)

  /** The Congruence that tries every child */
  def forSome1[A, X, Y, B, K](implicit V: Visitable[A, X, Y, B, K]) = new Congruence[X, Y, A, B] {
    def apply[F[_], M[_]](r: F[X] => M[F[Y]])(implicit F: Esrevart[F], M: MonadSearch[M]): F[A] => M[F[B]] = (fa: F[A]) => {

      val f: F[K] => M[Rotareti[M, F[X], F[Y], F[B]]] =
        (fk: F[K]) => F.traverse2FRot[M, K, A, X, Y, B](V.lens[Id, M](idInstances, M), V.default[Id](idInstances)[M](M))(M)(fk)(fa)

      def aux(s: Stream[F[K]]): M[F[B]] =
        if (s.isEmpty) M.empty[F[B]]
        else M.mtry(M.bind(f(s.head))(_.getAnswer(r)), aux(s.tail))

      val keys: Stream[F[K]] = F.traverse[Stream, A, K](fa)(V.keys)(streamInstances)

      aux(keys)
    }
  }

  /** The Congruence that tries every pair of children */
  def forSome2[A, X, Y, B, K](implicit V: Visitable[A, X, Y, B, K]) = new Congruence[(X, X), (Y, Y), A, B] {
    def apply[F[_], M[_]](r: F[(X, X)] => M[F[(Y, Y)]])(implicit F: Esrevart[F], M: MonadSearch[M]): F[A] => M[F[B]] = (fa: F[A]) => {

      val f: F[(K, K)] => M[Rotareti[M, F[(X, X)], F[(Y, Y)], F[B]]] =
        (fk: F[(K, K)]) => F.traverse2FRot[M, (K, K), A, (X, X), (Y, Y), B](V.lens[Pair, M](pairInstances, M), V.default[Pair](pairInstances)[M](M))(M)(fk)(fa)

      def auxi(i: Stream[F[K]]): M[F[B]] =
        if (i.isEmpty) M.empty[F[B]]
        else {
          def auxj(j: Stream[F[K]]): M[F[B]] =
            if (j.isEmpty) M.empty[F[B]]
            else {
              val ijhead: F[(K, K)] = F.zip[K, K](i.head, j.head)
              M.mtry(M.bind(f(ijhead))(_.getAnswer(r)), auxj(j.tail))
            }
          M.mtry(auxj(i.tail), auxi(i.tail))
        }

      val keys: Stream[F[K]] = F.traverse[Stream, A, K](fa)(V.keys)(streamInstances)

      auxi(keys)
    }
  }

  /** The Congruence that focuses on the collection of children */
  def down[A, X, Y, B, K](implicit V: Visitable[A, X, Y, B, K]): Congruence[Stream[X], Stream[Y], A, B] = Congruence.mapfs(V.allChildren[AnyMonadSearch](anyMonadSearch))

  def forAll1[A, X, Y, B, K](implicit V: Visitable[A, X, Y, B, K]): Congruence[X, Y, A, B] = {
    import zk._

    val stream: Congruence[X, Y, Stream[X], Stream[Y]] = Congruence.traverseStream[X, Y](V.default[Id](idInstances))
    down[A, X, Y, B, K] <==< stream
  }

  import Congruence._

  def innerMost[A, K](implicit V: Visitable[A, A, A, A, K]): Congruence[A, A, A, A] =
    (stry[A] <==< forAll1[A, A, A, A, K] <==< innerMost[A, K]) >=> repeat[A]

}

}

package zk.syntax {
  import zk._
  import scalaz.Traverse
  import scalaz.syntax.Ops


  final case class VisitableOps[A, X, Y, B, K](val self: A)(implicit V: Visitable[A, X, Y, B, K]) extends Ops[A] {
    def keys: Stream[K] = V.keys(self)

    def children[F[_], M[_]](lk: F[K])(implicit F: Traverse[F], M: MonadSearch[M]): M[Rotareti[M, F[X], F[Y], B]] =
      V.children[F, M](lk)(F, M)(self)

    def child1[M[_]](k: K)(implicit M: MonadSearch[M]): M[Rotareti[M, X, Y, B]] = V.child1[M](k)(M)(self)

    def child2[M[_]](k1: K, k2: K)(implicit M: MonadSearch[M]): M[Rotareti[M, (X, X), (Y, Y), B]] = V.child2[M](k1, k2)(M)(self)

    def allChildren[M[_]](implicit M: MonadSearch[M]): M[Rotareti[M, Stream[X], Stream[Y], B]] = V.allChildren[M](M)(self)
  }

  trait ToVisitableOps {
    final implicit def ToVisitableOps[A, X, Y, B, K](v: A)(implicit V: Visitable[A, X, Y, B, K]) = new VisitableOps[A, X, Y, B, K](v)(V)
  }

  trait VisitableSyntax[A, X, Y, B, K] {
    def V: Visitable[A, X, Y, B, K]

    final implicit def ToVisitableOps(v: A): VisitableOps[A, X, Y, B, K] = new VisitableOps[A, X, Y, B, K](v)(VisitableSyntax.this.V)
  }
}
/*
trait VisitableCompose[A,X,R,S,Y,B,K,L] extends Visitable[A,R,S,B,(K, L)] { H =>
  implicit val VL: Visitable[A, K, C]
  implicit val VR: Visitable[C, L, D]

  import VL.{KeysOrdering => KOrdering}
  import VR.{KeysOrdering => LOrdering}

  def keys: A => Stream[(K, L)] = (a: A) => {
    def aux(s: Stream[K]): Stream[(K, L)] =
      if (s.isEmpty) Stream.empty[(K, L)]
      else {
        val k1 = s.head
        VL.lens[Id, Option](a, k1)(idInstances, optionInstances) match {
          case None            => aux(s.tail)
          case Some(Answer(b)) => aux(s.tail)
          case Some(Next(f,c)) => VR.keys(f).map((l) => (k1, l)) ++ aux(s.tail)
        }
      }

    aux(VL.keys(a))
  }

  def children[F[_], M[_]](kl: F[(K, L)])(implicit F: Traverse[F], M: MonadSearch[M]): A => M[Zipper[A, F[D]]] = (a: A) => {
    type KL = (K, L)

    type TK[X] = TreeMap[K, X]
    val TK: Traverse[TK] = treeMapInstances[K]

    type TL[X] = TreeMap[L, X]
    val TL: Traverse[TL] = treeMapInstances[L]

    type SZ = Zipper[A, TK[C]]
    type NZ = Zipper[C, TL[D]]
    type CZ = Zipper[A, F[D]]

    type TKLD = TK[Zipper[C, TL[D]]]


    // All K keys in a TreeMap[K,K]
    val tmk: TK[K] = F.foldLeft[KL, TK[K]](kl, TreeMap.empty[K, K](VL.KeysOrdering))((tm: TK[K], p: KL) => tm + ((p._1, p._1)))

    // All L keys grouped by K in a TreeMap[K,TreeMap[L,L]]
    val tml: TK[TL[L]] = F.foldLeft[KL, TK[TL[L]]](kl, TreeMap.empty[K, TL[L]])((tm: TK[TL[L]], p: KL) =>
      tm + ((p._1, tm.get(p._1) match {
        case None => TreeMap.empty[L, L]
        case Some(tll) => tll + ((p._2, p._2))
      }))
    )

    // All the C children of A using self on K keys
    val selfChildren: M[SZ] = VL.children[TK, M](tmk)(TK, M)(a)

    M.bind[SZ, CZ](selfChildren)((z: SZ) => {

      import std.TreeMapFunctions._

      // Apply next on every C
      val nextChildrenMap: M[TKLD] =
        traverseTreeMap[M, K, C, NZ]((k: K, c: C) => tml.get(k) match {
          case None => M.empty[NZ]
          case Some(tll) => VR.children[TL, M](tll)(TL, M)(c)
        })(M, KOrdering)(z.focus)


      // Time to build the composed zipper
      M.apply[TKLD, CZ](nextChildrenMap)((tm: TKLD) => {

        // For every (K,L) we fetch D using the Map tm
        val traverseZipperAble: F[D] = F.map[KL, D](kl)((p: KL) => tm(p._1).focus(p._2))

        // Given F[KL,D] we fill tm with new values for D and rebuild A
        val context: F[D] => A = (newDs: F[D]) => {
          val skld: Stream[(KL, D)] = streamInstances.zip(F.toStream[KL](kl), F.toStream[D](newDs))

          // Fill tm with new values for D given by
          val tm2: TKLD = skld.foldLeft[TKLD](tm)((t: TKLD, v: (KL, D)) => {
            val (k, l, d) = (v._1._1, v._1._2, v._2)

            t.get(k) match {
              case None => t
              case Some(z2) => t + ((k, Zipper[C, TL[D]](z2.context, z2.focus + ((l, d)))))
            }
          })

          // Now that the new values for D are in place, we can rebuild every C
          val tc: TK[C] = TK.map(tm2)((nz: NZ) => nz.run)

          // Now that we have the new values for every C we can rebuild A
          z.context(tc)
        }

        // Return the zipper
        Zipper[A, F[D]](context, traverseZipperAble)
      })
    })
  }
}

*/
