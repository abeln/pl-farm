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
    }
  }

  def loop(): Unit = {
    print(">> ")
    val line = readLine()
    parseCmd(line) match {
      case Right(cmd) =>
        cmd match {
          case Assume(id, tpe) =>
            val closedTpe = close(tpe, treeMap)
            typeTree(closedTpe) match {
              case Right(WrapInf(Star)) =>
                val vTpe = evalTree(closedTpe)
                ctx = (Global(id), vTpe) :: ctx
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
    loop()
  }

  def main(args: Array[String]): Unit = {
    loop()
  }
}
