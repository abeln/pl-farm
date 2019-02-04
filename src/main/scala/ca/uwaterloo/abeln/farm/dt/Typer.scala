package ca.uwaterloo.abeln.farm.dt

import ca.uwaterloo.abeln.farm.dt.Names.Local
import ca.uwaterloo.abeln.farm.dt.Terms._
import ca.uwaterloo.abeln.farm.dt.Names.Name
import ca.uwaterloo.abeln.farm.dt.Results.{Result, error}
import ca.uwaterloo.abeln.farm.dt.Eval.{evalChk, emptyEnv, evalApp, evalCurriedApp}


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
       for {
         _ <- typeCheck(level, ctx, mot, VPi(VNat, _ => VStar))
         motVal = evalChk(mot, Nil)
         expZeroTpe = evalApp(motVal, VZero)
         _ <- typeCheck(level, ctx, base, expZeroTpe)
         expIndTpe = VPi(VNat, (prev: Value) => VPi(evalApp(motVal, prev), _ => evalApp(motVal, VSucc(prev))))
         _ <- typeCheck(level, ctx, ind, expIndTpe)
         _ <- typeCheck(level, ctx, num, VNat)
         numVal = evalChk(num, Nil)
       } yield evalApp(motVal, numVal)
      case TNil(tpe) =>
       for {
         _ <- typeCheck(level, ctx, tpe, VStar)
         vTpe = evalChk(tpe, Nil)
       } yield VVec(vTpe, VZero)
      case Vec(tpe, len) =>
       for {
         _ <- typeCheck(level, ctx, tpe, VStar)
         vTpe = evalChk(tpe, Nil)
         _ <- typeCheck(level, ctx, len, VNat)
         vLen = evalChk(len, Nil)
       } yield VStar
      case Cons(tpe, len, head, tail) =>
       for {
         _ <- typeCheck(level, ctx, tpe, VStar)
         vTpe = evalChk(tpe, Nil)
         _ <- typeCheck(level, ctx, len, VNat)
         vLen = evalChk(len, Nil)
         _ <- typeCheck(level, ctx, head, vTpe)
         vHead = evalChk(head, Nil)
         _ <- typeCheck(level, ctx, tail, VVec(vTpe, vLen))
         vTail = evalChk(tail, Nil)
       } yield VVec(vTpe, VSucc(vLen))
      case VecElim(tpe, motive, base, ind, argLen, argVec) =>
       for {
         _ <- typeCheck(level, ctx, tpe, VStar)
         vTpe = evalChk(tpe, Nil)
         expMotiveTpe = VPi(VNat, (len: Value) => VPi(VVec(vTpe, len), (ignore: Value) => VStar))
         _ <- typeCheck(level, ctx, motive, expMotiveTpe)
         vMotive = evalChk(motive, Nil)
         expBaseTpe = evalCurriedApp(vMotive, VZero, VNil(vTpe))
         _ <- typeCheck(level, ctx, base, expBaseTpe)
         vBase = evalChk(base, Nil)
         expIndTpe = VPi(
           VNat,
           (len: Value) =>
             VPi(vTpe,
               (head: Value) =>
                 VPi(VVec(vTpe, len),
                   (tail: Value) => {
                     val evidenceTpe = evalCurriedApp(vMotive, len, tail)
                     val expTpe = evalCurriedApp(vMotive, VSucc(len), VCons(vTpe, len, head, tail))
                     VPi(evidenceTpe, _ => expTpe)
                   }
             )))
         _ <- typeCheck(level, ctx, ind, expIndTpe)
         vInd = evalChk(ind, Nil)
         _ <- typeCheck(level, ctx, argLen, VNat)
         vLen = evalChk(argLen, Nil)
         _ <- typeCheck(level, ctx, argVec, VVec(vTpe, vLen))
         vVec = evalChk(argVec, Nil)
       } yield evalCurriedApp(vMotive, vLen, vVec)
      case TEq(tpe, a, b) =>
       for {
         _ <- typeCheck(level, ctx, tpe, VStar)
         vTpe = evalChk(tpe, Nil)
         _ <- typeCheck(level, ctx, a, vTpe)
         _ <- typeCheck(level, ctx, b, vTpe)
       } yield VStar
      case Refl(tpe, e) =>
       for {
         _ <- typeCheck(level, ctx, tpe, VStar)
         vTpe = evalChk(tpe, Nil)
         _ <- typeCheck(level, ctx, e, vTpe)
         vE = evalChk(e, Nil)
       } yield VEq(vTpe, vE, vE)
      case EqElim(tpe, mot, prop, a, b, ev) =>
       for {
         _ <- typeCheck(level, ctx, tpe, VStar)
         vTpe = evalChk(tpe, Nil)
         expMotTpe = VPi(vTpe, (x: Value) => VPi(vTpe, (y: Value) => VPi(VEq(vTpe, x, y), (ev: Value) => VStar)))
         _ <- typeCheck(level, ctx, mot, expMotTpe)
         vMot = evalChk(mot, Nil)
         expPropTpe = VPi(vTpe, z => evalCurriedApp(vMot, z, z, VRefl(vTpe, z)))
         _ <- typeCheck(level, ctx, prop, expPropTpe)
         vProp = evalChk(prop, Nil)
         _ <- typeCheck(level, ctx, a, vTpe)
         vA = evalChk(a, Nil)
         _ <- typeCheck(level, ctx, b, vTpe)
         vB = evalChk(b, Nil)
         _ <- typeCheck(level, ctx, ev, VEq(vTpe, vA, vB))
         vEv = evalChk(ev, Nil)
       } yield evalCurriedApp(vMot, vA, vB, vEv)
    }
//    println(s"inf level = $level term = $term ctx = $ctx res = $res")
    res
  }

  def checkEquiv(term: InfTerm, res: Type, exp: Type): Result[Type] = {
    if (equiv(res, exp)) Right(res)
    else error(s"term: ${showChk0(WrapInf(term))} expected: ${showTpe(exp)}, but got ${showTpe(res)}")
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
