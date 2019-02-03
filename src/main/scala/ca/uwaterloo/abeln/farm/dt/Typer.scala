package ca.uwaterloo.abeln.farm.dt

import ca.uwaterloo.abeln.farm.dt.Names.Local
import ca.uwaterloo.abeln.farm.dt.Terms._
import ca.uwaterloo.abeln.farm.dt.Names.Name
import ca.uwaterloo.abeln.farm.dt.Results.{Result, error}
import ca.uwaterloo.abeln.farm.dt.Eval.{evalChk, emptyEnv, evalApp}


object Typer {

  type Context = List[(Name, Type)]

  val emptyCtx: Context = Nil

  def lookup(ctx: Context, name: Name): Option[Type] = {
    for (pair <- ctx.find(_._1 == name)) yield pair._2
  }

  def typeInf0(ctx: Context, term: InfTerm): Result[Type] = {
    typeInf(level = 0, ctx, term)
  }

  def typeInf(level: Int, ctx: Context, term: InfTerm): Result[Type] = {
   val res = term match {
      case Ann(term1, tpe) =>
        for {
          _ <- typeCheck(level, ctx, tpe, VStar)
          vTpe = evalChk(tpe, emptyEnv)
          _ <- typeCheck(level, ctx, term1, vTpe)
        } yield vTpe
      case Star => Right(VStar)
      case Pi(from, to) =>
        for {
          _ <- typeCheck(level, ctx, from, VStar)
          vFrom = evalChk(from, emptyEnv)
          fv = Local(level)
          ctx1 = (fv, vFrom) :: ctx
          to1 = substCheck(0, to, Free(fv))
          _ <- typeCheck(level + 1, ctx1, to1, VStar)
        } yield VStar
      case bound: Bound => error(s"unexpected bound identifier: $bound")
      case Free(name) => lookup(ctx, name) match {
        case Some(tpe) => Right(tpe)
        case _ => error(s"not bound to a type: $name")
      }
      case App(fn, arg) =>
        typeInf(level, ctx, fn) match {
          case Right(VPi(from, to)) =>
            for {
              _ <- typeCheck(level, ctx, arg, from)
              vArg = evalChk(arg, emptyEnv)
            } yield to(vArg)
          case Right(wrongTpe) =>
            error(s"expected a dependent function type, but got: $wrongTpe")
          case err: Left[String, Type] => err
        }
      case Nat => Right(VStar)
      case Zero => Right(VNat)
      case Succ(pred) =>
       for {
         _ <- typeCheck(level, ctx, pred, VNat)
       } yield VNat
      case NatElim(mot, base, ind, num) =>
       val res = for {
         _ <- typeCheck(level, ctx, mot, VPi(VNat, _ => VStar))
         motVal = evalChk(mot, Nil)
         expZeroTpe = evalApp(motVal, VZero)
         _ <- typeCheck(level, ctx, base, expZeroTpe)
         expIndTpe = VPi(VNat, (prev: Value) => VPi(evalApp(motVal, prev), _ => evalApp(motVal, VSucc(prev))))
         _ <- typeCheck(level, ctx, ind, expIndTpe)
         _ <- typeCheck(level, ctx, num, VNat)
         numVal = evalChk(num, Nil)
       } yield evalApp(motVal, numVal)
       res
    }
//    println(s"inf level = $level term = $term ctx = $ctx res = $res")
    res
  }

  def checkEquiv(term: InfTerm, res: Type, exp: Type): Result[Type] = {
    if (equiv(res, exp)) Right(res)
    else error(s"term: $term, expected: $exp, but got $res")
  }

  def typeCheck(level: Int, ctx: Context, term: ChkTerm, proto: Type): Result[Unit] = {
    val res = term match {
      case WrapInf(term1) =>
        for {
          res <- typeInf(level, ctx, term1)
          _ <- checkEquiv(term1, res, proto)
        } yield ()
      case Lam(body) =>
        proto match {
          case VPi(from, to) =>
            val name = Local(level)
            val ctx1 = (name, from) :: ctx
            val body1 = substCheck(0, body, Free(name))
            for {
              _ <- typeCheck(level + 1, ctx1, body1, to(vfree(name)))
            } yield ()
          case _ => error(s"typing a lambda, but proto is $proto")
        }
    }
//    println(s"chk level = $level term = $term proto = $proto ctx = $ctx")
    res
  }
}
