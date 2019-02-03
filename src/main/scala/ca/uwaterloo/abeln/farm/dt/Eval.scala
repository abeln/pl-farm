package ca.uwaterloo.abeln.farm.dt

import ca.uwaterloo.abeln.farm.dt.Terms._

object Eval {

  type Env = List[Value]

  val emptyEnv = List.empty[Value]

  def evalApp(fnVal: Value, argVal: Value): Value = {
    fnVal match {
      case VLam(semFn) => semFn(argVal)
      case _ => VNeutral(NApp(fnVal, argVal))
    }
  }

  def evalInf(term: InfTerm, env: Env): Value = {
    term match {
      case Ann(term1, _) => evalChk(term1, env)
      case Star => VStar
      case Pi(from, to) =>
        val fromVal = evalChk(from, env)
        VPi(fromVal, (arg: Value) => evalChk(to, arg :: env))
      case Bound(binder) => env(binder)
      case Free(name) => vfree(name)
      case App(fn, arg) =>
        val fnVal = evalInf(fn, env)
        val argVal = evalChk(arg, env)
        evalApp(fnVal, argVal)
      case Nat => VNat
      case Zero => VZero
      case Succ(n) => VSucc(evalChk(n, env))
      case NatElim(motive, base, ind, num) =>
        val vMot = evalChk(motive, env)
        val vBase = evalChk(base, env)
        val vInd = evalChk(ind, env)
        val vNum = evalChk(num, env)
        def elim(currNum: Value): Value = {
          currNum match {
            case VZero => vBase
            case VSucc(n) =>
              evalApp(evalApp(vInd, n), elim(n))
            case _ =>
              VNeutral(NNatElim(vMot, vBase, vInd, currNum))
          }
        }
        elim(vNum)
    }
  }

  def evalChk(term: ChkTerm, env: Env): Value = {
    term match {
      case WrapInf(term1) => evalInf(term1, env)
      case Lam(term1) => VLam((argVal: Value) => evalChk(term1, argVal :: env))
    }
  }
}
