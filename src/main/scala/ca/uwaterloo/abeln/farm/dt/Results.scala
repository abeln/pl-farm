package ca.uwaterloo.abeln.farm.dt

object Results {
  type Result[T] = Either[String, T]

  def error[T](msg: String): Result[T] = Left(msg)
}
