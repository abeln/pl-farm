package ca.uwaterloo.abeln.farm.dt

import scala.io.StdIn.readLine
import Parsers.{Expr, Let, parseCmd}

object Repl {

  def loop(): Unit = {
    print(">> ")
    val line = readLine()
    parseCmd(line) match {
      case Right(cmd) =>
        cmd match {
          case Let(id, expr) => ???
          case Expr(expr) =>
            println(Terms.removeNames0(expr))
        }
      case Left(err) => println(s"error: $err")
    }
    loop()
  }

  def main(args: Array[String]): Unit = {
    loop()
  }
}
