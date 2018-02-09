package adversaria.tests

import estrapade.{TestApp, test}
import contextual.data.scalac._
import contextual.data.fqt._
import annotation.StaticAnnotation

import adversaria._

final case class id() extends StaticAnnotation
final case class count(number: Int) extends StaticAnnotation

case class Person(name: String, @id email: String)

@count(10)
case class Company(name: String)

case class Employee(person: Person, @id code: Long)

object Tests extends TestApp {

  def tests(): Unit = {
    test("get annotations on type") {
      implicitly[TypeAnnotations[Company]].annotations
    }.assert(_ == List(count(10)))

    test("find the field with a particular annotation") {
      val ann = implicitly[AnnotatedParam[id, Person]]
      val person = Person("John Smith", "test@example.com")
      ann.get(person)
    }.assert(_ == "test@example.com")
    
    test("check that implicit for missing annotation is not resolved") {
      scalac"implicitly[AnnotatedParam[id, Company]]"
    }.assert(_ == TypecheckError("adversaria: could not find a parameter annotated with type @adversaria.tests.id"))

    test("extract annotation value generically") {
      def getId[T](value: T)(implicit anns: AnnotatedParam[id, T]): String =
        anns.get(value).toString

      getId(Employee(Person("John Smith", "test@example.com"), 3141592))
    }.assert(_ == "3141592")

  }
}
