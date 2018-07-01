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

import language.experimental.macros
import scala.reflect.macros.whitebox

import totalitarian._

object Macros {
  def typeError[T1, T, F <: Base: c.WeakTypeTag, D <: Base: c.WeakTypeTag](c: whitebox.Context)(
      from: c.Expr[Result[T1, F]]): c.Expr[Result[T, D]] = {
    import c.universe._


    def unpack(typ: Type): List[Type] = typ.dealias.etaExpand match {
      case RefinedType(types, _) => types.flatMap(unpack(_))
      case one =>
        List(one)
    }

    val found = unpack(weakTypeOf[F]).flatMap(_.typeArgs).to[Set]
    val desired = unpack(weakTypeOf[D]).flatMap(_.typeArgs).to[Set]
    val missing = found -- desired

    def mkType(types: Set[Type]): String =
      ("~" :: types.map(_.toString).to[List]).mkString(" | ")

    //c.info(c.enclosingPosition, s"mitigation: the failure type of the Result type does not match the expected types\n\n permitted: ${mkType(desired)}\n     found: ${mkType(found)}\nunexpected: ${mkType(missing)}", true)
    c.abort(c.enclosingPosition, "")
  }

  def generalTypeError[T: c.WeakTypeTag, F <: Base: c.WeakTypeTag, R: c.WeakTypeTag](c: whitebox.Context)(
      from: c.Expr[Result[T, F]]): c.Expr[R] = {
    import c.universe._
    
    def unpack(typ: Type): List[Type] = typ match {
      case RefinedType(types, _) => types.flatMap(unpack(_))
      case one => List(one)
    }

    val found = unpack(weakTypeOf[F]).flatMap(_.typeArgs).to[Set]

    def mkType(types: Set[Type]): String =
      ("~" :: types.map(_.toString).to[List].filter(_ == "~")).mkString(" | ")

    c.info(c.enclosingPosition, s"mitigation: type mismatch involving Result type\n\n   found: Result[${weakTypeOf[T]}, ${mkType(found)}]\nexpected: ${weakTypeOf[R]}", true)
    c.abort(c.enclosingPosition, "")
  }

  def generalTypeError2[T: c.WeakTypeTag, R <: Base: c.WeakTypeTag, F: c.WeakTypeTag](c: whitebox.Context)(
      from: c.Expr[F]): c.Expr[Result[T, R]] = {
    import c.universe._
    
    def unpack(typ: Type): List[Type] = typ match {
      case RefinedType(types, _) => types.flatMap(unpack(_))
      case one => List(one)
    }

    val expected = unpack(weakTypeOf[R]).flatMap(_.typeArgs).to[Set]

    def mkType(types: Set[Type]): String =
      ("~" :: types.map(_.toString).to[List].filter(_ == "~")).mkString(" | ")

    c.info(c.enclosingPosition, s"mitigation: type mismatch involving Result type\n\nexpected: Result[${weakTypeOf[T]}, ${mkType(expected)}]\n   found: ${weakTypeOf[R]}", true)
    c.abort(c.enclosingPosition, "")
  }

}
