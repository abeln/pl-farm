package ca.uwaterloo.abeln.farm.dt

import ca.uwaterloo.abeln.farm.dt.Terms._

object Eval {

  type Env = List[Value]

  val emptyEnv = List.empty[Value]

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
        def evalApp(fnVal: Value, argVal: Value): Value = {
          fnVal match {
            case VLam(semFn) => semFn(argVal)
            case VNeutral(neutral) => VNeutral(NApp(neutral, argVal))
            case VStar => VNeutral(NApp(NStar, argVal))
            case VPi(from, to) => VNeutral(NApp(NPi(from, to), argVal))
          }
        }
        val fnVal = evalInf(fn, env)
        val argVal = evalChk(arg, env)
        evalApp(fnVal, argVal)
    }
  }

  def evalChk(term: ChkTerm, env: Env): Value = {
    term match {
      case WrapInf(term1) => evalInf(term1, env)
      case Lam(term1) => VLam((argVal: Value) => evalChk(term1, argVal :: env))
    }
  }
}
