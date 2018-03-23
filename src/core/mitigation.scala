/*
  
  Mitigation, version 1.0.0. Copyright 2018 Jon Pretty, Propensive Ltd.

  The primary distribution site is: https://propensive.com/

  Licensed under the Apache License, Version 2.0 (the "License"); you may not use
  this file except in compliance with the License. You may obtain a copy of the
  License at
  
      http://www.apache.org/licenses/LICENSE-2.0
 
  Unless required by applicable law or agreed to in writing, software
  distributed under the License is distributed on an "AS IS" BASIS, WITHOUT
  WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the
  License for the specific language governing permissions and limitations under
  the License. */


package mitigation

import language.higherKinds
import language.existentials
import language.implicitConversions

import scala.reflect.ClassTag

import scala.util._, control.NonFatal

import totalitarian._, ident.Disjunct

object `package` {
  implicit def mitigate[T, E <: Part](block: => T): Mitigable[T, E] =
    new Mitigable(() => block)

  type ![T <: Throwable] = totalitarian.![T]

  def on[T](implicit key: ident.Key[T, _]): OfType[T, key.Value, ident.type] =
    totalitarian.ident.on[T]

  def otherwise(implicit key: ident.Key[Surprise[_], _]): OfType[Surprise[_], key.Value, ident.type] =
    totalitarian.ident.on[Surprise[_]]
}

class Mitigable[T, E <: Part](val fn: () => T) extends AnyVal {
  
  def unary_~[TConst[_, _ <: Part]](implicit mitigation: Mitigation[TConst]): TConst[T, E] =
    mitigation(fn())
}

object Mitigation {

  type Drop[Tc[_]] = ({ type Two[T, E <: Part] = Tc[T] })

  implicit val options: Mitigation[Drop[Option]#Two] =
    new Mitigation[Drop[Option]#Two] {
      def apply[T, E <: Part](fn: => T): Option[T] =
        try Some(fn) catch { case NonFatal(_) => None }
    }

  implicit val tries: Mitigation[Drop[Try]#Two] =
    new Mitigation[Drop[Try]#Two] {
      def apply[T, E <: Part](fn: => T): Try[T] = Try(fn)
    }
  
  implicit val results: Mitigation[Result] =
    new Mitigation[Result] {
      def apply[T, E <: Part](fn: => T): Result[T, E] = Result(fn)
    }
}

trait Mitigation[TConst[_, _ <: Part]] { def apply[T, E <: Part](fn: => T): TConst[T, E] }

object Result {
  def apply[T, E <: Part](fn: => T): Result[T, E] = expect(Answer(fn))
  
  def expect[T, E <: Part](result: => Result[T, E]): Result[T, E] =
    try result catch { case NonFatal(exception) => Surprise(exception) }

  def rescue[From <: Exception]: Rescue[From] = new Rescue[From](0)

}

class Rescue[From <: Exception](val nothing: Int) extends AnyVal {
  def apply[To <: Exception: TypeId, T](fn: From => To)(block: => T)(implicit ev: ClassTag[From]): Result[T, ![To]] = try Answer(block) catch {
    case e: From => Errata(None, Disjunct(fn(e)))
    case NonFatal(e) => Surprise(e)
  }
}

sealed trait Result[Type, -E <: Part] {

  def map[S](fn: Type => S): Result[S, E] = this match {
    case Answer(value) =>
      Result.expect(Answer(fn(value)))
    case Errata(Some(value), initial, ensuing @ _*) =>
      Result.expect(Errata(Some(fn(value)), initial, ensuing: _*))
    case Errata(None, initial, ensuing @ _*) =>
      Errata(None, initial, ensuing: _*)
    case Surprise(exception) =>
      Surprise(exception)
  }
  
  def flatMap[S, E2 <: Part](fn: Type => Result[S, E2]): Result[S, E with E2] = this match {
    case Answer(value) => Result.expect(fn(value))
    case Errata(None, initial, ensuing @ _*) => Errata(None, initial, ensuing: _*)
    case Errata(Some(value), initial, ensuing @ _*) =>
      Result.expect(fn(value)) match {
        case Answer(value) =>
          Errata(Some(value), initial, ensuing: _*)
        case Errata(optValue, initial2, ensuing2 @ _*) =>
          Errata(optValue, initial, initial2 +: (ensuing2 ++ ensuing): _*)
        case Surprise(exception) =>
          Surprise(exception)
      }
    case Surprise(exception) => Surprise(exception)
  }

  def opt: Option[Type]
  def unsafeGet: Type = opt.get
  def success: Boolean
  def exceptions: List[Throwable]


  def recover[T <: Throwable, T2 <: ![T], V, W](
    cases: Disjunct.MapClause[T, T2, Type, Type, V, W]*)(
    implicit ev: Disjunct.AllCases[T2, E with ![Surprise[_]]]): Type
}

case class Answer[Type](value: Type) extends Result[Type, Part] {
  def opt: Option[Type] = Some(value)
  def success: Boolean = true
  def exceptions: List[Throwable] = Nil

  def recover[T <: Throwable, T2 <: ![T], V, W](
    cases: Disjunct.MapClause[T, T2, Type, Type, V, W]*)(
    implicit ev: Disjunct.AllCases[T2, Part with ![Surprise[_]]]): Type = value
}

case class Surprise[Type](error: Throwable) extends Throwable with Result[Type, Part] {
  def opt: Option[Type] = None
  def success: Boolean = false
  def exceptions: List[Throwable] = List(error)
  
  def recover[T <: Throwable, T2 <: ![T], V, W](
    cases: Disjunct.MapClause[T, T2, Type, Type, V, W]*)(
    implicit ev: Disjunct.AllCases[T2, Part with ![Surprise[_]]]): Type = {
      throw error
  }
}

case class Errata[Type, E <: Part](
  optValue: Option[Type],
  initial: Disjunct[E],
  ensuing: Disjunct[E]*
)
    extends Result[Type, E] {
  def opt: Option[Type] = optValue
  def failures: List[Disjunct[E]] = initial +: ensuing.to[List]
  def success: Boolean = false

  def exceptions: List[Throwable] = failures.map(_.value match { case e: Throwable => e })

  def recover[T <: Throwable, T2 <: ![T], V, W](
    cases: Disjunct.MapClause[T, T2, Type, Type, V, W]*)(
    implicit ev: Disjunct.AllCases[T2, E with ![Surprise[_]]]): Type = {
    val thisCase = cases.find(_.fromTypeTag == initial.typeId).get
    thisCase.action(initial.value.asInstanceOf[V])
  }
}

