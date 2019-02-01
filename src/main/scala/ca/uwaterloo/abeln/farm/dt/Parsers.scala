package ca.uwaterloo.abeln.farm.dt

import scala.util.parsing.combinator.JavaTokenParsers

object Parsers extends JavaTokenParsers {

  def parseCmd(text: String): Either[String, Cmd] = {
    parse(cmd, text) match {
      case Success(res, _) => Right(res)
      case _ => Left(s"can't parse '$text'")
    }
  }

  sealed trait Cmd
  case class Let(id: String, term: Tree) extends Cmd
  case class Expr(tree: Tree) extends Cmd

  def cmd: Parser[Cmd] = let | expr
  def let: Parser[Cmd] = sexp(("let" ~> ident) ~ tree) ^^ { case ~(id, expr) => Let(id, expr) }
  def expr: Parser[Cmd] = tree ^^ Expr

  sealed trait Tree
  case class Ann(term: Tree, tpe: Tree) extends Tree
  case object Star extends Tree
  case class Pi(binder: String, from: Tree, to: Tree) extends Tree
  case class Arrow(from: Tree, to: Tree) extends Tree
  case class Var(name: String) extends Tree
  case class App(fn: Tree, arg: Tree) extends Tree
  case class Lam(binder: String, body: Tree) extends Tree

  def sexp[T](p: Parser[T]): Parser[T] = ("(" ~> p) <~ ")"

  def tree: Parser[Tree] = ann | star | pi | arrow | free | app | lam
  def ann: Parser[Tree] =  sexp(("::" ~> tree) ~ tree) ^^ { case ~(term, tpe) => Ann(term, tpe) }
  def star: Parser[Tree] = "*" ^^ { _ => Star }
  def pi: Parser[Tree] = sexp(("pi" ~> ident) ~ (tree ~ tree)) ^^ {
    case ~(id, ~(from, to)) => Pi(id, from, to)
  }
  def arrow: Parser[Tree] = sexp("=>" ~> (tree ~ tree)) ^^ {
    case ~(from, to) => Arrow(from, to)
  }
  def free: Parser[Tree] = ident ^? { case id if id != "*" => Var(id) }
  def app: Parser[Tree] = sexp(tree ~ tree) ^^ { case ~(fn, arg) => App(fn, arg) }
  def lam: Parser[Tree] = sexp(("lam" ~> ident) ~ tree) ^^ { case ~(binder, body) => Lam(binder, body) }
}
