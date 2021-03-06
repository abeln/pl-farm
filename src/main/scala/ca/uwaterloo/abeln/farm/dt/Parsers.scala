package ca.uwaterloo.abeln.farm.dt

import ca.uwaterloo.abeln.farm.dt.Terms.TEq

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
  case class Assume(id: String, tpe: Tree) extends Cmd
  case class Expr(tree: Tree) extends Cmd

  def cmd: Parser[Cmd] = let | assume | expr
  def let: Parser[Cmd] = sexp(("let" ~> ident) ~ tree) ^^ { case ~(id, expr) => Let(id, expr) }
  def expr: Parser[Cmd] = tree ^^ Expr
  def assume: Parser[Cmd] = sexp(("assume" ~> ident) ~ tree) ^^ { case ~(id, tpe) => Assume(id, tpe) }

  sealed trait Tree
  case class Ann(term: Tree, tpe: Tree) extends Tree
  case object Star extends Tree
  case class Pi(binder: String, from: Tree, to: Tree) extends Tree
  case class Arrow(from: Tree, to: Tree) extends Tree
  case class Var(name: String) extends Tree
  case class App(fn: Tree, arg: Tree) extends Tree
  case class Lam(binder: String, body: Tree) extends Tree
  case class Num(n: Int) extends Tree
  case class NatElim(motive: Tree, base: Tree, ind: Tree, num: Tree) extends Tree
  case object Nat extends Tree
  case class Succ(prev: Tree) extends Tree
  case class TNil(tpe: Tree) extends Tree
  case class Vec(tpe: Tree, len: Tree) extends Tree
  case class Cons(tpe: Tree, len: Tree, head: Tree, tail: Tree) extends Tree
  case class VecElim(tpe: Tree, mot: Tree, base: Tree, ind: Tree, len: Tree, arg: Tree) extends Tree
  case class TEq(tpe: Tree, a: Tree, b: Tree) extends Tree
  case class Refl(tpe: Tree, e: Tree) extends Tree
  case class EqElim(tpe: Tree, motive: Tree, prop: Tree, a: Tree, b: Tree, ev: Tree) extends Tree


  def sexp[T](p: Parser[T]): Parser[T] = ("(" ~> p) <~ ")"

  def tree: Parser[Tree] = ann | star | pi | arrow | nat | free | lam | num | natElim | succ | tnil | vec | cons | vecElim | teq | refl | eqElim | app

  def ann: Parser[Tree] =  sexp(("::" ~> tree) ~ tree) ^^ { case ~(term, tpe) => Ann(term, tpe) }
  def star: Parser[Tree] = "*" ^^ { _ => Star }
  def pi: Parser[Tree] = sexp(("Pi" ~> ident) ~ (tree ~ tree)) ^^ {
    case ~(id, ~(from, to)) => Pi(id, from, to)
  }
  def arrow: Parser[Tree] = sexp("=>" ~> (tree ~ tree)) ^^ {
    case ~(from, to) => Arrow(from, to)
  }
  def free: Parser[Tree] = ident ^? { case id if id != "*" => Var(id) }
  def app: Parser[Tree] = sexp(tree ~ rep1(tree)) ^^ {
    case ~(fn, args) =>
      args.foldLeft(fn) {
        case (fn1, arg) => App(fn1, arg)
      }
  }
  def lam: Parser[Tree] = sexp(("lam" ~> ident) ~ tree) ^^ { case ~(binder, body) => Lam(binder, body) }
  def num: Parser[Tree] = decimalNumber ^^ { decStr => Num(decStr.toInt) }

  def nat: Parser[Tree] = "Nat" ^^ { _ => Nat }

  def natElim: Parser[Tree] = sexp(((("natElim" ~> tree) ~ tree) ~ tree) ~ tree) ^^ {
    case ~(~(~(mot, base), ind), num) => NatElim(mot, base, ind, num)
  }

  def succ: Parser[Tree] = sexp("succ" ~> tree) ^^ Succ

  def tnil: Parser[Tree] = sexp("nil" ~> tree) ^^ TNil

  def vec: Parser[Tree] = sexp("Vec" ~> (tree ~ tree)) ^^ {
    case ~(tpe, len) => Vec(tpe, len)
  }

  def cons: Parser[Tree] = sexp("cons" ~> (((tree ~ tree) ~ tree) ~ tree)) ^^ {
    case ~(~(~(tpe, len), head), tail) =>
      Cons(tpe, len, head, tail)
  }

  def vecElim: Parser[Tree] = sexp("vecElim" ~> (((((tree ~ tree) ~ tree) ~ tree) ~ tree) ~ tree)) ^^ {
    case ~(~(~(~(~(tpe, mot), base), ind), len), vec) =>
      VecElim(tpe, mot, base, ind, len, vec)
  }

  def teq: Parser[Tree] = sexp("Eq" ~> ((tree ~ tree) ~ tree)) ^^ {
    case ~(~(tpe, a), b) => TEq(tpe, a, b)
  }

  def refl: Parser[Tree] = sexp("refl" ~> (tree ~ tree)) ^^ {
    case ~(tpe, elem) => Refl(tpe, elem)
  }

  def eqElim: Parser[Tree] = sexp("eqElim" ~> (tree ~ (tree ~ (tree ~ (tree ~ (tree ~ tree)))))) ^^ {
    case ~(tpe, ~(mot, ~(prop, ~(a, ~(b, ev))))) =>
      EqElim(tpe, mot, prop, a, b, ev)
  }
}
