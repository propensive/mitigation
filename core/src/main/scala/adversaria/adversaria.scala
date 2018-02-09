package adversaria

import annotation.StaticAnnotation
import annotation.implicitNotFound
import language.experimental.macros
import collection.immutable.ListMap

import scala.reflect._, reflect.macros._

object Macros {
  
  def typeAnnotations[T: c.WeakTypeTag](c: blackbox.Context): c.Tree = {
    import c.universe._
    val sym = c.weakTypeOf[T].typeSymbol
    val typeAnnotations = sym.annotations.map(_.tree).map(c.untypecheck(_))
    val constructor = sym.asClass.primaryConstructor
    val params = constructor.asMethod.typeSignature.paramLists.head.map(_.asTerm)
    
    val paramAnnotations = params.map { p =>
      val annotations = p.annotations.map(_.tree).map(c.untypecheck(_))
      q"(${p.name.decodedName.toString}, _root_.scala.List(..${annotations}))"
    }

    q"""_root_.adversaria.TypeAnnotations(
      _root_.scala.List(..$typeAnnotations),
      _root_.scala.collection.immutable.ListMap(..$paramAnnotations)
    )"""
  }

  def annotatedParam[A <: StaticAnnotation: c.WeakTypeTag,
                     T: c.WeakTypeTag](c: whitebox.Context): c.Tree = {
    import c.universe._
    
    val sym = c.weakTypeOf[T].typeSymbol
    val const = sym.asClass.primaryConstructor
    val params = const.asMethod.typeSignature.paramLists.head.map(_.asTerm)

    val param = params.find { p =>
      val annotations = p.annotations.map(_.tree)
      annotations.exists(_.tpe =:= c.weakTypeOf[A])
    }.getOrElse(c.abort(c.enclosingPosition, "adversaria: could not find matching annotation"))

    val annotations = param.annotations.map(_.tree)
    val ann = c.untypecheck(annotations.find(_.tpe =:= c.weakTypeOf[A]).get)

    q"""
      new _root_.adversaria.AnnotatedParam[${weakTypeOf[A]}, ${weakTypeOf[T]}]($ann) {
        def get(t: ${weakTypeOf[T]}): Return = t.${param.name} ; type Return = ${param.info}
      }
    """
  }
}

object TypeAnnotations {
  implicit def annotations[T]: TypeAnnotations[T] = macro Macros.typeAnnotations[T]
}

object AnnotatedParam {
  implicit def param[A <: StaticAnnotation, T]: AnnotatedParam[A, T] =
    macro Macros.annotatedParam[A, T]
}

case class TypeAnnotations[T](annotations: List[StaticAnnotation],
                              parameters: ListMap[String, List[StaticAnnotation]])

@implicitNotFound("adversaria: could not find a parameter annotated with type @${A}")
abstract class AnnotatedParam[A <: StaticAnnotation, T](val annotation: A) {
  type Return
  def get(t: T): Return
}

