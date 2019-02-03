package ca.uwaterloo.abeln.farm.dt

object Predef {

  val defs: List[String] =
    """
      | (assume Bool *)
      | (assume true Bool)
      | (assume false Bool)
      |
      | (let plus (:: (lam arg (nelim (lam m (=> Nat Nat)) (lam n n) (lam n (lam prevFn (lam x (succ (prevFn x))))) arg)) (=> Nat (=> Nat Nat))))
      |
      | (let v1 (cons Nat 1 1 (cons Nat 0 2 (nil Nat))))
      | (let v2 (cons Nat 1 3 (cons Nat 0 4 (nil Nat))))
      |
      | (let append (:: (lam len1 (lam vec1 (lam len2 (lam vec2 (velim Nat (lam len (lam vec (Vec Nat ((plus len) len2)))) vec2 (lam len (lam head (lam tail (lam prev (cons Nat ((plus len) len2) head prev))))) len1 vec1))))) (pi len1 Nat (pi vec1 (Vec Nat len1) (pi len2 Nat (pi vec2 (Vec Nat len2) (Vec Nat ((plus len1) len2))))))))
      |
      | ((((append 2) v1) 2) v2)
      |
    """.stripMargin.lines.toList
}
