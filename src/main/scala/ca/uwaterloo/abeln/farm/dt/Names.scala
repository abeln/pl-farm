package ca.uwaterloo.abeln.farm.dt

object Names {

  sealed trait Name
  case class Global(name: String) extends Name
  case class Local(id: Int) extends Name
  case class Quote(id: Int) extends Name
}
