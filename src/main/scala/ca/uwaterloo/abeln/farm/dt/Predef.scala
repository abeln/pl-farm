package ca.uwaterloo.abeln.farm.dt

object Predef {

  val defs: List[String] =
    """
      | (assume Bool *)
      | (assume true Bool)
      | (assume false Bool)
      |
      | (let plus (:: (lam arg (nelim (lam m (=> Nat Nat)) (lam n n) (lam n (lam prevFn (lam x (succ (prevFn x))))) arg)) (=> Nat (=> Nat Nat))))
    """.stripMargin.lines.toList
}
