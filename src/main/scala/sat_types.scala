package my.sat

/** Essential solver types */

object Var {
  type t = Int
  def toInt(v:t) = v
  def apply(v:t) = v
}

class Lit(v:Var.t, sign:Boolean) {
  val x = if (sign) v + v + 1 else v + v 
  def toInt = x
}

object Lit {
  def apply(v:Var.t, sign:Boolean) = new Lit(v,sign)
}
