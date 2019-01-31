package ca.uwaterloo.abeln.farm.dt

import scala.util.parsing.combinator.JavaTokenParsers

object Parsers extends JavaTokenParsers {

//  sealed trait Tree
//  case class Ann(term: Tree, tpe: Type) extends Tree
//  case class Var(name: String) extends Tree
//  case class App(fn: Tree, arg: Tree) extends Tree
//  case class Lam(binder: String, body: Tree) extends Tree
//
//  def sexp[T](p: Parser[T]): Parser[T] = ("(" ~> p) <~ ")"
//
//  def tree: Parser[Tree] = ann | free | app | lam
//  def ann: Parser[Tree] =  sexp(("::" ~> tree) ~ tpe) ^^ { case ~(term, tpe) => Ann(term, tpe) }
//  def free: Parser[Tree] = ident ^^ { Var }
//  def app: Parser[Tree] = sexp(tree ~ tree) ^^ { case ~(fn, arg) => App(fn, arg) }
//  def lam: Parser[Tree] = sexp(("\\" ~> ident) ~ tree) ^^ { case ~(binder, body) => Lam(binder, body) }
//
//  def tpe: Parser[Type] = tfree | tfun
//  def tfree: Parser[Type] = ???
//  def tfun: Parser[Type] = ???
}
