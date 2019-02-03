package ca.uwaterloo.abeln.farm.dt

object Predef {

  val defs: List[String] =
    """
      | (assume Bool *)
      | (assume true Bool)
      | (assume false Bool)
    """.stripMargin.lines.toList
}
