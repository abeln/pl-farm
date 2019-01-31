package ca.uwaterloo.abeln.farm.dt

import ca.uwaterloo.abeln.farm.dt.Names.{Name, Quote}

object Terms {

  sealed trait InfTerm
  case class Ann(term: ChkTerm, tpe: ChkTerm) extends InfTerm
  case object Star extends InfTerm
  case class Pi(from: ChkTerm, to: ChkTerm) extends InfTerm
  case class Bound(binder: Int) extends InfTerm
  case class Free(name: Name) extends InfTerm
  case class App(fn: InfTerm, arg: ChkTerm) extends InfTerm

  sealed trait ChkTerm
  case class WrapInf(term: InfTerm) extends ChkTerm
  case class Lam(term: ChkTerm) extends ChkTerm

  sealed trait Value
  case class VLam(lam: Value => Value) extends Value
  case object VStar extends Value
  case class VPi(from: Value, to: Value => Value) extends Value
  case class VNeutral(neutral: Neutral) extends Value

  sealed trait Neutral
  case class NFree(name: Name) extends Neutral
  case class NApp(fn: Neutral, arg: Value) extends Neutral
  case object NStar extends Neutral
  case class NPi(from: Value, to: Value => Value) extends Neutral

  type Type = Value // dependent types!

  def vfree(name: Name): Value = VNeutral(NFree(name))

  def substInf(level: Int, term: InfTerm, free: Free): InfTerm = {
    term match {
      case Ann(term1, tpe) => Ann(substCheck(level, term1, free), tpe)
      case Star => Star
      case Pi(from, to) => Pi(substCheck(level + 1, from, free), substCheck(level + 1, to, free))
      case Bound(binder) =>
        if (binder == level) free
        else term
      case _: Free => term
      case App(fn, arg) => App(substInf(level, fn, free), substCheck(level, arg, free))
    }
  }

  def substCheck(level: Int, term: ChkTerm, free: Free): ChkTerm = {
    term match {
      case WrapInf(term1) => WrapInf(substInf(level, term1, free))
      case Lam(body) => Lam(substCheck(level + 1, body, free))
    }
  }

  def equiv(tp1: Value, tp2: Value): Boolean = {
    quote0(tp1) == quote0(tp2)
  }

  def quote0(tp: Value): ChkTerm = quote(0, tp)

  def quote(level: Int, tp: Value): ChkTerm = {
    tp match {
      case VLam(fn) =>
        val fv = vfree(Quote(level))
        Lam(quote(level + 1, fn(fv)))
      case VStar => WrapInf(Star)
      case VPi(from, to) =>
        val fv = vfree(Quote(level))
        WrapInf(Pi(quote(level, from), quote(level + 1, to(fv))))
      case VNeutral(neutral) => WrapInf(quoteNeutral(level, neutral))
    }
  }

  def quoteNeutral(level: Int, neutral: Neutral): InfTerm = {
    neutral match {
      case NFree(name) => boundFree(level, name)
      case NApp(fn, arg) => App(quoteNeutral(level, fn), quote(level, arg))
      case NStar => Star
      case NPi(from, to) =>
        val from1 = quote(level, from)
        val fv = vfree(Quote(level))
        val to1 = quote(level + 1, to(fv))
        Pi(from1, to1)
    }
  }

  def boundFree(level: Int, name: Name): InfTerm = {
    name match {
      case Quote(j) => Bound(level - j - 1)
      case _ => Free(name)
    }
  }
}
