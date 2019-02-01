package ca.uwaterloo.abeln.farm.dt

import scala.io.StdIn.readLine
import Parsers.{Expr, Let, parseCmd}
import Terms._
import Typer.{Context, emptyCtx, typeInf0}
import ca.uwaterloo.abeln.farm.dt.Names.Global
import ca.uwaterloo.abeln.farm.dt.Results.Result

object Repl {

  var ctx: Context = emptyCtx

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

  def loop(): Unit = {
    print(">> ")
    val line = readLine()
    parseCmd(line) match {
      case Right(cmd) =>
        cmd match {
          case Let(id, tpeExpr) =>
            typeTree(tpeExpr) match {
              case Right(WrapInf(Star)) =>
                ctx = (Global(id), VStar) :: ctx
              case _: Right[String, ChkTerm] =>
                println("expected a type in the rhs of a let")
              case Left(err) => println(s"type error: $err")
            }
          case Expr(expr) =>
            typeTree(expr) match {
              case Right(chkTerm) => println(s"$chkTerm")
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
