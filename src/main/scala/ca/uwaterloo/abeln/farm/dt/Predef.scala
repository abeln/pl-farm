package ca.uwaterloo.abeln.farm.dt

object Predef {

  val defs: List[String] =
    """
      | (assume Bool *)
      | (assume true Bool)
      | (assume false Bool)
      |
      | (let plus (:: (lam arg (natElim (lam m (=> Nat Nat)) (lam n n) (lam n (lam prevFn (lam x (succ (prevFn x))))) arg)) (=> Nat (=> Nat Nat))))
      |
      | (let v1 (cons Nat 1 1 (cons Nat 0 2 (nil Nat))))
      | (let v2 (cons Nat 1 3 (cons Nat 0 4 (nil Nat))))
      |
      | (let append (:: (lam len1 (lam vec1 (lam len2 (lam vec2 (vecElim Nat (lam len (lam vec (Vec Nat ((plus len) len2)))) vec2 (lam len (lam head (lam tail (lam prev (cons Nat ((plus len) len2) head prev))))) len1 vec1))))) (Pi len1 Nat (Pi vec1 (Vec Nat len1) (Pi len2 Nat (Pi vec2 (Vec Nat len2) (Vec Nat ((plus len1) len2))))))))
      |
      | ((((append 2) v1) 2) v2)
      |
      | (let eqTpe (Pi a Nat (Pi b Nat (=> (Eq Nat a b) (Eq Nat b a)))))|
      | (let eqSymm (:: (lam a (lam b (lam ev (eqElim Nat (lam a (lam b (lam ev (Eq Nat b a)))) (lam z (refl Nat z)) a b ev)))) eqTpe))
      |
      |
    """.stripMargin.lines.toList
}
