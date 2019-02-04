package ca.uwaterloo.abeln.farm.dt

import scala.io.StdIn.readLine
import Parsers.{Assume, Expr, Let, Tree, parseCmd}
import Terms._
import Typer.{Context, emptyCtx, typeInf0}
import ca.uwaterloo.abeln.farm.dt.Names.Global
import ca.uwaterloo.abeln.farm.dt.Results.Result

object Repl {

  var ctx: Context = emptyCtx
  val P = Parsers

  var treeMap: Map[String, P.Tree] = Map.empty[String, P.Tree]

  def typeTree(tree: Parsers.Tree): Result[ChkTerm] = {
    removeNamesInf0(tree) match {
      case Right(infTerm) =>
        typeInf0(ctx, infTerm) match {
          case Right(tpe) => Right(quote0(tpe): ChkTerm)
          case Left(err) => Left(err)
        }
      case Left(err) => Left(err)
    }
  }

  def evalTree(tree: Parsers.Tree): Value = { // TODO: return in a monad
    val infTerm = removeNamesInf0(tree).asInstanceOf[Right[String, InfTerm]].value
    Eval.evalInf(infTerm, Nil)
  }

  def close(tree: Tree, tmap: Map[String, P.Tree]): Tree = {
    def cl(tree: Tree) = close(tree, tmap)
    tree match {
      case P.Ann(term, tpe) => P.Ann(close(term, tmap), close(tpe, tmap))
      case P.Star => P.Star
      case P.Pi(binder, from, to) =>
        val tmap1 = tmap - binder
        P.Pi(binder, close(from, tmap1), close(to, tmap1))
      case P.Arrow(from, to) => P.Arrow(close(from, tmap), close(to, tmap))
      case P.Var(name) =>
        if (tmap.contains(name)) tmap(name) else P.Var(name)
      case P.App(fn, arg) => P.App(close(fn, tmap), close(arg, tmap))
      case P.Lam(binder, body) =>
        val tmap1 = tmap - binder
        P.Lam(binder, close(body, tmap1))
      case P.Num(n) => P.Num(n)
      case P.NatElim(mot, base, ind, num) =>
        P.NatElim(close(mot, tmap), close(base, tmap), close(ind, tmap), close(num, tmap))
      case P.Nat => P.Nat
      case P.Succ(prev) => P.Succ(close(prev, tmap))
      case P.TNil(tpe) => P.TNil(cl(tpe))
      case P.Vec(tpe, len) => P.Vec(cl(tpe), cl(len))
      case P.Cons(tpe, len, head, tail) =>
        P.Cons(cl(tpe), cl(len), cl(head), cl(tail))
      case P.VecElim(tpe, mot, base, ind, len, arg) =>
        P.VecElim(cl(tpe), cl(mot), cl(base), cl(ind), cl(len), cl(arg))
      case P.TEq(tpe, a, b) =>
        P.TEq(cl(tpe), cl(a), cl(b))
      case P.Refl(tpe, e) =>
        P.Refl(cl(tpe), cl(e))
      case P.EqElim(tpe, mot, prop, a, b, ev) =>
        P.EqElim(cl(tpe), cl(mot), cl(prop), cl(a), cl(b), cl(ev))
    }
  }

  def proc(line: String): Unit = {
    parseCmd(line) match {
      case Right(cmd) =>
        cmd match {
          case Assume(id, tpe) =>
            val closedTpe = close(tpe, treeMap)
            typeTree(closedTpe) match {
              case Right(WrapInf(Star)) =>
                val vTpe = evalTree(closedTpe)
                ctx = (Global(id), vTpe) :: ctx
                println(s"(assume $id ${showChk0(quote0(vTpe))})")
              case _: Right[String, ChkTerm] =>
                println("error: expected a type in the rhs of a let")
              case Left(err) => println(s"type error: $err")
            }
          case Let(id, expr) =>
            val expr1 = close(expr, treeMap)
            typeTree(expr1) match {
              case Right(chkTerm) =>
                treeMap = treeMap + (id -> expr1)
                println(s"$id :: ${showChk0(chkTerm)}")
              case Left(err) => println(s"type error: $err")
            }
          case Expr(expr) =>
            val expr1 = close(expr, treeMap)
            typeTree(expr1) match {
              case Right(chkTerm) =>
                println(s"${showChk0(quote0(evalTree(expr1)))} :: ${showChk0(chkTerm)}")
              case Left(err) => println(s"type error: $err")
            }
        }
      case Left(err) => println(s"parse error: $err")
    }
  }

  def repl(): Unit = {
    Predef.defs.filter(_.trim.nonEmpty).foreach(proc)
    def loop(): Unit = {
      print(">> ")
      var prog = ""
      var parensCount = 0
      do {
        val line = readLine()
        parensCount += line.foldLeft(0) {
          case (acc, c) =>
            c match {
              case '(' => acc + 1
              case ')' => acc - 1
              case _ => acc
            }
        }
        prog += (" " + line)
      } while (parensCount > 0)
      proc(prog)
      loop()
    }
    loop()
  }

  def main(args: Array[String]): Unit = {
    repl()
  }
}
