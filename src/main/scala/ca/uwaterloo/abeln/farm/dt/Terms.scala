package ca.uwaterloo.abeln.farm.dt

import ca.uwaterloo.abeln.farm.dt.Names.{Global, Name, Quote}
import ca.uwaterloo.abeln.farm.dt.Parsers.Tree
import ca.uwaterloo.abeln.farm.dt.Results.{Result, error}

object Terms {

  sealed trait InfTerm
  case class Ann(term: ChkTerm, tpe: ChkTerm) extends InfTerm
  case object Star extends InfTerm
  case class Pi(from: ChkTerm, to: ChkTerm) extends InfTerm
  case class Bound(binder: Int) extends InfTerm
  case class Free(name: Name) extends InfTerm
  case class App(fn: InfTerm, arg: ChkTerm) extends InfTerm
  case object Nat extends InfTerm
  case object Zero extends InfTerm
  case class Succ(n: ChkTerm) extends InfTerm
  case class NatElim(motive: ChkTerm, base: ChkTerm, ind: ChkTerm, num: ChkTerm) extends InfTerm

  sealed trait ChkTerm
  case class WrapInf(term: InfTerm) extends ChkTerm
  case class Lam(term: ChkTerm) extends ChkTerm

  sealed trait Value
  case class VLam(lam: Value => Value) extends Value
  case object VStar extends Value
  case class VPi(from: Value, to: Value => Value) extends Value
  case class VNeutral(neutral: Neutral) extends Value
  case object VNat extends Value
  case object VZero extends Value
  case class VSucc(n: Value) extends Value

  sealed trait Neutral
  case class NValue(value: Value) extends Neutral
  case class NFree(name: Name) extends Neutral
  case class NApp(fn: Value, arg: Value) extends Neutral
  case class NNatElim(motive: Value, base: Value, ind: Value, num: Value) extends Neutral

  type Type = Value // dependent types!

  def vfree(name: Name): Value = VNeutral(NFree(name))

  def substInf(level: Int, term: InfTerm, free: Free): InfTerm = {
    def recChk(term: ChkTerm): ChkTerm = {
      substCheck(level, term, free)
    }
    term match {
      case Ann(term1, tpe) => Ann(substCheck(level, term1, free), tpe)
      case Star => Star
      case Pi(from, to) => Pi(recChk(from), substCheck(level + 1, to, free))
      case Bound(binder) =>
        if (binder == level) free
        else term
      case _: Free => term
      case App(fn, arg) => App(substInf(level, fn, free), recChk(arg))
      case Nat => Nat
      case Zero => Zero
      case Succ(prev) => Succ(substCheck(level, prev, free))
      case NatElim(motive, base, ind, num) =>
        NatElim(recChk(motive), recChk(base), recChk(ind), recChk(num))
    }
  }

  def substCheck(level: Int, term: ChkTerm, free: Free): ChkTerm = {
    term match {
      case WrapInf(term1) => WrapInf(substInf(level, term1, free))
      case Lam(body) => Lam(substCheck(level + 1, body, free))
    }
  }

  def equiv(vl1: Value, vl2: Value): Boolean = {
    quote0(vl1) == quote0(vl2)
  }

  def quote0(vl: Value): ChkTerm = quote(0, vl)

  def quoteInf(level: Int, vl: Value): InfTerm = {
    quote(level, vl) match {
      case WrapInf(infTerm) => infTerm
      case _ => sys.error("internal error: quoteInf0 internal error")
    }
  }

  def quote(level: Int, vl: Value): ChkTerm = {
    vl match {
      case VLam(fn) =>
        val fv = vfree(Quote(level))
        Lam(quote(level + 1, fn(fv)))
      case VStar => WrapInf(Star)
      case VPi(from, to) =>
        val fv = vfree(Quote(level))
        WrapInf(Pi(quote(level, from), quote(level + 1, to(fv))))
      case VNeutral(neutral) => WrapInf(quoteNeutral(level, neutral))
      case VZero => WrapInf(Zero)
      case VSucc(pred) => WrapInf(Succ(quote(level, pred)))
      case VNat => WrapInf(Nat)
    }
  }

  def quoteNeutral(level: Int, neutral: Neutral): InfTerm = {
    neutral match {
      case NFree(name) => boundFree(level, name)
      case NApp(fn, arg) => App(quoteInf(level, fn), quote(level, arg))
      case NNatElim(motive, base, ind, num) =>
        NatElim(quote(level, motive), quote(level, base), quote(level, ind), quote(level, num))
      case NValue(vl) => quoteInf(level, vl)
    }
  }

  def boundFree(level: Int, name: Name): InfTerm = {
    name match {
      case Quote(j) => Bound(level - j - 1)
      case _ => Free(name)
    }
  }

  def removeNamesInf0(tree: Tree): Result[InfTerm] = {
    removeNamesChk0(tree) match {
      case Right(WrapInf(inf)) => Right(inf)
      case Right(term) => error(s"expected an inf term, but got: $term")
      case Left(err) => Left(err)
    }
  }

  def removeNamesChk0(tree: Tree): Result[ChkTerm] = removeNamesChk(tree, Nil)

  def removeNamesChk(tree: Tree, ctx: List[String]): Result[ChkTerm] = {
    val P = Parsers
    tree match {
      case P.Ann(term, tpe) =>
        for {
          term1 <- removeNamesChk(term, ctx)
          tpe1 <- removeNamesChk(tpe, ctx)
        } yield WrapInf(Ann(term1, tpe1))
      case P.Star => Right(WrapInf(Star))
      case P.Pi(binder, from, to) =>
        for {
          from1 <- removeNamesChk(from, ctx)
          to1 <- removeNamesChk(to, binder :: ctx)
        } yield WrapInf(Pi(from1, to1))
      case P.Arrow(from, to) =>
        val ctx1 = "" :: ctx // augment the context with a dummy binder
        for {
          from1 <- removeNamesChk(from, ctx)
          to1 <- removeNamesChk(to, ctx1)
        } yield WrapInf(Pi(from1, to1))
      case P.Var(name) =>
        ctx.indexWhere(_ == name) match {
          case -1 => Right(WrapInf(Free(Global(name))))
          case index => Right(WrapInf(Bound(index)))

        }
      case P.App(fn, arg) =>
        def checkInf(fn: ChkTerm): Result[ChkTerm] = {
          fn match {
            case WrapInf(_) => Right(fn)
            case _: Lam => Left(s"expected an inf term on the lhs of an app")
          }
        }
        def toInf(term: ChkTerm): InfTerm = term.asInstanceOf[WrapInf].term
        for {
          fn1 <- removeNamesChk(fn, ctx)
          _ <- checkInf(fn1)
          arg1 <- removeNamesChk(arg, ctx)
        } yield WrapInf(App(toInf(fn1), arg1))
      case P.Lam(binder, body) =>
        for {
          body1 <- removeNamesChk(body, binder :: ctx)
        } yield Lam(body1)
      case P.Num(n) =>
        def expand(n: Int): ChkTerm = {
          assert(n >= 0)
          if (n == 0) WrapInf(Zero)
          else WrapInf(Succ(expand(n - 1)))
        }
        Right(expand(n))
      case P.NatElim(mot, base, ind, num) =>
        for {
          motTerm <- removeNamesChk(mot, ctx)
          baseTerm <- removeNamesChk(base, ctx)
          indTerm <- removeNamesChk(ind, ctx)
          numTerm  <- removeNamesChk(num, ctx)
        } yield WrapInf(NatElim(motTerm, baseTerm, indTerm, numTerm))
      case P.Nat => Right(WrapInf(Nat))
    }
  }


  def showChk0(term: ChkTerm): String = {
    showChk(level = 0, term, Nil)
  }

  def showChk(level: Int, term: ChkTerm, names: List[String]): String = {
    term match {
      case WrapInf(term1) => showInf(level, term1, names)
      case Lam(term1) =>
        val binder = s"x$level"
        s"λ$binder." ++ showChk(level + 1, term1, binder :: names)
    }
  }

  def showInf(level: Int, term: InfTerm, names: List[String]): String = {
    term match {
      case Ann(term1, tpe) => "(" ++ showChk(level, term1, names) ++ ")" ++ " :: " ++ showChk(level, tpe, names)
      case Star => "*"
      case Pi(from, to) =>
        val binder = s"x$level"
        s"∀($binder: ${showChk(level, from, names)}).${showChk(level + 1, to, binder :: names)}"
      case Bound(binder) => names(binder)
      case Free(name) =>
        name match {
          case Global(nameStr) => nameStr
          case _ => sys.error(s"unexpected name $name")
        }
      case App(fn, arg) => "(" ++ showInf(level, fn, names) ++ ") " ++ showChk(level, arg, names)
      case Nat => "Nat"
      case Zero => "0"
      case succ@Succ(pred) =>
        numToDec(WrapInf(succ)) match {
          case Some(dec) => dec.toString
          case None =>
            s"Succ(${showChk(level, pred, names)})"
        }
      case NatElim(motive, base, ind, num) =>
        def recChk(term: ChkTerm): String = showChk(level, term, names)
        s"natElim(${recChk(motive)}, ${recChk(base)}, ${recChk(ind)}, ${recChk(num)})"
    }
  }

  def numToDec(num: ChkTerm): Option[Int] = {
    num match {
      case WrapInf(Succ(prev)) =>
        for {
          p <- numToDec(prev)
        } yield p + 1
      case WrapInf(Zero) => Some(0)
      case _ => None
    }
  }
}
