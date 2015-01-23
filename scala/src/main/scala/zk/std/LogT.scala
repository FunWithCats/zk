package zk.std

import zk.{MonadTransSearch, MonadSearch}

/** Logging Monad Transformer */
final case class LogT[M[_], A](val run : M[A])

/** Instances satisfied by the Logging Monad Transformer */
trait LogTInstances extends MonadTransSearch[LogT] { self =>
  def balise(b: String, i:Any) : String = "<" + b + ">" + i + "</" + b + ">\n"
  def log(s : String) = {
    println("<log>")
    println(s)
    println("</log>")
  }


  
  def liftM[M[_], A](ma: M[A])(implicit M: MonadSearch[M]): LogT[M, A] = LogT[M, A](ma)

  trait MonadTransSearchApply[M[_]] extends MonadSearch[({type λ[α] = LogT[M, α]})#λ] {  MT =>
    implicit val M: MonadSearch[M]

    def point[A](a: => A): LogT[M, A] = LogT[M, A](M.point[A](a))

    def bind[A, B](fa: LogT[M, A])(f: (A) => LogT[M, B]): LogT[M, B] =
      LogT[M,B](M.bind[A,B](fa.run)((a:A) => {
        log(balise("binding", balise("context", fa) + balise("value" , a)))
        val res = f(a).run
        log(balise("binding", balise("context", fa) + balise("value" , a) + balise("result" , res)))
        res
      }))

    def empty[A]: LogT[M, A] = LogT[M,A](M.empty[A])

    def plus[A](ma: LogT[M, A], mb: => LogT[M, A]): LogT[M, A] =
      LogT[M,A]( M.plus[A]( { log(balise("plus" ,   balise("side" , "left")
                                                  + balise("left" , ma.run)
                                                  + balise("right" , mb.run)
                                         ))
                               ma.run
                            }
                          , { log(balise("plus" ,   balise("side" , "right")
                                                  + balise("left" , ma.run)
                                                  + balise("right" , mb.run)
                                        ))
                               mb.run
                            }
                          ))

    def local[A](ma: LogT[M, A]): LogT[M, A] = LogT[M,A](M.local[A]({
      log(balise("local" , ma.run))
      ma.run
    } ) )

    def mtry[A](ma: LogT[M, A], mb: => LogT[M, A]): LogT[M, A] =
      LogT[M,A]( M.mtry[A]( { log(balise("mtry" ,   balise("side" , "then")
                                                  + balise("then" , ma.run)
                                                  + balise("else" , mb.run)
                                         ))
                               ma.run
                            }
                          , { log(balise("mtry" ,   balise("side" , "right")
                                                  + balise("then" , ma.run)
                                                  + balise("else" , mb.run)
                                        ))
                               mb.run
                            }
                          ))
  }

  implicit def apply[M[_]](implicit pM: MonadSearch[M]): MonadSearch[({type λ[α] = LogT[M, α]})#λ] =
    new MonadTransSearchApply[M] {
      val M = pM
    }
}
