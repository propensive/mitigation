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
  the License.

*/

package mitigation

import language.higherKinds
import language.existentials
import language.implicitConversions
import language.experimental.macros

import totalitarian._, ident.Disjunct

import scala.reflect.ClassTag
import scala.util._, control.NonFatal
import scala.annotation.unchecked.uncheckedVariance

object `package` {
  implicit def mitigate[T, E <: Base](block: => T): Mitigable[T, E] =
    new Mitigable(() => block)

  type ![T <: Throwable] = totalitarian.![T]
  type |[A, B <: Throwable] = A with ![B]
  type ~ = Base

  def on[T](implicit key: ident.Key[T, _]): OfType[T, key.Value, ident.type] =
    totalitarian.ident.on[T]

  def otherwise(implicit key: ident.Key[Surprise[_], _]): OfType[Surprise[_], key.Value, ident.type] =
    totalitarian.ident.on[Surprise[_]]
}

object Mitigable {

  class Apply[E <: Base](val nothing: Int) extends AnyVal {
    def apply[T](block: => T): Mitigable[T, E] = new Mitigable(() => block)
  }

  def apply[E <: Base]: Apply[E] = new Apply(0)
}

class Mitigable[T, E <: Base](val fn: () => T) extends AnyVal {
  
  def unary_~[TConst[_, _ <: Base]](implicit mitigation: Mitigation[TConst]): TConst[T, E] =
    mitigation(fn())
}

object Mitigation {

  type Drop[Tc[_]] = ({ type Two[T, E <: Base] = Tc[T] })

  implicit val options: Mitigation[Drop[Option]#Two] =
    new Mitigation[Drop[Option]#Two] {
      def apply[T, E <: Base](fn: => T): Option[T] =
        try Some(fn) catch { case NonFatal(_) => None }
    }

  implicit val tries: Mitigation[Drop[Try]#Two] =
    new Mitigation[Drop[Try]#Two] {
      def apply[T, E <: Base](fn: => T): Try[T] = Try(fn)
    }
  
  implicit val results: Mitigation[Result] =
    new Mitigation[Result] {
      def apply[T, E <: Base](fn: => T): Result[T, E] = Result(fn)
    }
}

trait Mitigation[TConst[_, _ <: Base]] { def apply[T, E <: Base](fn: => T): TConst[T, E] }

object Result extends Result_1 {
  def apply[T, E <: Base](fn: => T): Result[T, E] = expect(Answer(fn))

  def ascribe[T, E <: Throwable: TypeId](exception: => E)(option: Option[T]): Result[T, ~ | E] =
    option match {
      case None => Aborted(Disjunct(exception))
      case Some(value) => Answer(value)
    }

  def sequence[T, E <: Base](xs: List[Result[T, E]]): Result[List[T], E] =
    xs.foldLeft(Answer(List[T]()): Result[List[T], E]) { case (acc, next) =>
      acc.flatMap { list => next.map(_ :: list) }
    }.map(_.reverse)

  def expect[T, E <: Base](result: => Result[T, E]): Result[T, E] =
    try result catch { case NonFatal(exception) => Surprise(exception) }

  def rescue[From <: Exception]: Rescue[From] = new Rescue[From](0)

  //implicit def typeError[T1, T, F <: Base, D <: Base](from: Result[T1, F]): Result[T, D] =
  //  macro Macros.typeError[T1, T, F, D]

  def answer[T](value: T): Result[T, ~] = Answer(value)
  def abort[T, E <: Throwable: TypeId](exception: E): Result[T, Base with ![E]] = Aborted(Disjunct(exception))
  def erratum[T, E <: Throwable: TypeId](value: T, exception: E): Result[T, ~ | E] = Errata(value, Disjunct(exception))
  def surprise[T](exception: Throwable) = Surprise[T](exception)
}

trait Result_1 {
  //implicit def generalTypeError[T, F <: Base, R](from: Result[T, F]): R =
  //  macro Macros.generalTypeError[T, F, R]
  
  //implicit def generalTypeError2[T, R <: Base, F](from: F): Result[T, R] =
  //  macro Macros.generalTypeError2[T, R, F]
}

class Rescue[From <: Exception](val nothing: Int) extends AnyVal {
  def apply[To <: Exception: TypeId, T](fn: From => To)(block: => T)(implicit ev: ClassTag[From]): Result[T, ![To]] = try Answer(block) catch {
    case e: From => Aborted(Disjunct(fn(e)))
    case NonFatal(e) => Surprise(e)
  }

  def apply[To <: Exception: TypeId, T](exception: => To)(block: => T)(implicit ev: ClassTag[From]): Result[T, ![To]] =
    apply[To, T] { (e: From) => exception } (block)
}

case class Filtered() extends Exception

sealed trait Result[+Type, -E <: Base] {

  final def map[S](fn: Type => S): Result[S, E] = this match {
    case Answer(value) =>
      Result.expect(Answer(fn(value)))
    case Errata(value, initial, ensuing @ _*) =>
      Result.expect(Errata(fn(value), initial, ensuing: _*))
    case Aborted(initial, ensuing @ _*) =>
      Aborted(initial, ensuing: _*)
    case Surprise(exception) =>
      Surprise(exception)
  }

  final def foreach(fn: Type => Unit): Unit = {
    map[Unit](fn(_))
    ()
  }

  final def filter(fn: Type => Boolean): Result[Type, E with ![Filtered]] = this match {
    case Answer(value) =>
      if(fn(value)) Answer(value) else Aborted(Disjunct(Filtered()))
    case Errata(value, initial, ensuing @ _*) =>
      Aborted(initial, (ensuing :+ Disjunct(Filtered())): _*)
    case other => other
  }

  def withFilter(fn: Type => Boolean): Result[Type, E with ![Filtered]] = filter(fn)

  def escalate[E2 <: Exception: TypeId](exception: => E2): Result[Type, E with ![E2]] = this match {
    case Errata(value, initial, ensuing @ _*) => Aborted(Disjunct(exception), (initial +: ensuing): _*)
    case Answer(value) => Answer(value)
    case Surprise(surprise) => Surprise(surprise)
    case Aborted(terminal, preceding @ _*) => Aborted(terminal, preceding: _*)
  }

  final def flatMap[S, E2 <: Base](fn: Type => Result[S, E2]): Result[S, E with E2] = this match {
    case Answer(value) => Result.expect(fn(value))
    case Errata(value, initial, ensuing @ _*) =>
      Result.expect(fn(value)) match {
        case Answer(value) => Errata(value, initial, ensuing: _*)
        case Aborted(terminal, preceding @ _*) => Aborted(terminal, preceding: _*)
        case Surprise(exception) => Surprise(exception)
        case Errata(value, initial2, ensuing2 @ _*) =>
          Errata(value, initial, initial2 +: (ensuing2 ++ ensuing): _*)
      }
    case Aborted(terminal, preceding @ _*) => Aborted(terminal, preceding: _*)
    case Surprise(exception) => Surprise(exception)
  }

  def opt: Option[Type]
  def unsafeGet: Type = opt.get
  def successful: Boolean
  def errata: List[Disjunct[E]]
  def exceptions: List[Throwable] = errata.map(_.value match { case e: Throwable => e })

  // replaces any sort of failure
  def remedy[T >: Type](value: => T): Result[T, Base] = this match {
    case Answer(value) => Answer(value)
    case Errata(oldValue, initial, ensuing @ _*) => Answer(value)
    case Surprise(error) => Surprise(error)
    case Aborted(terminal, preceding @ _*) => Answer(value)
  }

  def downplay[T >: Type](value: => T): Result[T, E] = this match {
    case Answer(value) => Answer(value)
    case Errata(value, initial, ensuing @ _*) => Errata(value, initial, ensuing: _*)
    case Surprise(error) => Surprise(error)
    case Aborted(terminal, preceding @ _*) => Errata(value, terminal, preceding: _*)
  }

  // Disregards errata, but not aborted
  def abide[T >: Type](value: T): Result[T, E] = this match {
    case Answer(value) => Answer(value)
    case Errata(value, initial, ensuing @ _*) => Answer(value)
    case Surprise(error) => Surprise(error)
    case Aborted(terminal, preceding @ _*) => Aborted(terminal, preceding :_*)
  }

  def recover[T <: Throwable, T2 <: ![T], V, W](cases: MapClause[T, T2, Type @uncheckedVariance, Type, V, W, ident.type]*)(implicit ev: Disjunct.AllCases[T2, E]): Type = this match {
    case Answer(value) => value
    case Aborted(terminal, preceding @ _*) =>
      val thisCase = cases.find(_.fromTypeTag == terminal.typeId).get
      thisCase.action(terminal.value.asInstanceOf[V])
    case Errata(value, initial, ensuing @ _*) =>
      val thisCase = cases.find(_.fromTypeTag == initial.typeId).get
      thisCase.action(initial.value.asInstanceOf[V])
    case Surprise(exception) =>
      val thisCase = cases.find(_.fromTypeTag == implicitly[TypeId[Surprise[_]]]).get
      thisCase.action(Surprise(exception).asInstanceOf[V])
  }

  def consolidate[T <: Throwable, T2 <: ![T], R, R2, V, W](cases: MapClause[T, T2, R, R2, V, W, ident.type]*)(implicit ev: Disjunct.AllCases[T2, E]): Result[Type, Base with W] = this match {
    case Answer(value) => Answer(value)
    case Aborted(terminal, preceding @ _*) =>
      Aborted(terminal.map(cases: _*), preceding.map { p => p.map(cases: _*) }: _*)
    case Errata(value, initial, ensuing @ _*) =>
      Errata(value, initial.map(cases: _*), ensuing.map { p => p.map(cases: _*) }: _*)
    case Surprise(exception) =>
      Surprise(exception)
  }
  
  def repair[T <: Throwable, T2 <: ![T], V, W <: Base](cases: MapClause[T, T2, Result[Type @uncheckedVariance, W], Result[Type, W], V, W, ident.type]*)(implicit ev: Disjunct.AllCases[T2, E]): Result[Type, Base with W] = this match {
    case Answer(value) => Answer(value)
    case Surprise(exception) => Surprise(exception)
    case Aborted(terminal, preceding @ _*) =>
      terminal.map(cases: _*)
    case Errata(value, initial, ensuing @ _*) =>
      initial.map(cases: _*)
  }
}

case class Answer[Type](value: Type) extends Result[Type, Base] {
  def opt: Option[Type] = Some(value)
  def successful: Boolean = true
  def errata: List[Disjunct[Base]] = Nil
}

case class Surprise[Type](error: Throwable) extends Throwable with Result[Type, Base] {
  def opt: Option[Type] = None
  def successful: Boolean = false
  override def exceptions: List[Throwable] = List(error)
  def errata: List[Disjunct[Base]] = Nil
}

case class Aborted[Type, E <: Base](terminal: Disjunct[E], preceding: Disjunct[E]*) extends Result[Type, E] {

  def successful: Boolean = false
  def opt: Option[Type] = None
  def errata: List[Disjunct[E]] = preceding.to[List] :+ terminal
}

case class Errata[Type, E <: Base](
  value: Type,
  initial: Disjunct[E],
  ensuing: Disjunct[E]*
)
    extends Result[Type, E] {
  def opt: Option[Type] = None
  def errata: List[Disjunct[E]] = initial +: ensuing.to[List]
  def successful: Boolean = false
}

