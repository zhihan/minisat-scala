package my.sat

/** Essential solver types */

object Var {
  type t = Int
  def toInt(v:t) = v
  def apply(v:t) = v

  val undef = -1
}

class LBool(val v: Byte) {
  override def equals(other:Any) = {
    other match {
      case that:LBool => (v == that.v)
      case _ => false
    }
  }
  def xor(sgn:Boolean) = if (sgn) LBool((-v).toByte) else LBool(v)
  override def toString = {
    if (v == -1) "FALSE"
    else if (v == 1) "TRUE"
    else if (v == 0) "UNKNOWN"
    else "ERROR: UNKNOWN VALUE"
  }
}

object LBool {
  val False = new LBool(-1)
  val True = new LBool(1)
  val Unknown = new LBool(0)
  def apply(v:Byte) = new LBool(v)
  def apply(v:Boolean) = if (v) new LBool(1) else new LBool(-1)
}

/** Literal
 * A literal is either a variable (unsigned) or its negation (signed).
 * 
 */
final class Lit(v:Var.t, sgn:Boolean) {
  val x = if (sgn) v + v + 1 else v + v 
  
  def sign = (x & 1) == 1
  def variable = x >> 1 
  def toInt = x
  override def equals (other: Any) = {
    other match {
      case that:Lit => (x == that.x)
      case _ => false
    }
  }
  override def toString = {
    if (sign) "!L(" + v.toString + ")" 
    else "L(" + v.toString + ")"
  }
}

object Lit {
  def apply(v:Var.t, sign:Boolean) = new Lit(v,sign)
  def not(l:Lit) = new Lit(l.variable, !l.sign)

  
  val undef = Lit(Var.undef, false)  // Special constants
  val error = Lit(Var.undef, true) 

}

/** Clause
 * A clause contains a vector of literals
 * 
 */
class Clause(lits: Array[Lit], 
	     val learnt:Boolean) {
  // Header info

  var mark = 0 // A 2-bit flag

  var lit = lits.clone // Local copy, mutable 

  // The following was implemented as union in MiniSAT.
  var activity = if (learnt) 0.0 else -1.0 // Only useful for learnt
  var abst = calcAbstraction

  def calcAbstraction = {
    // Abstraction computes a uint32 representation of 
    // the bit vector corresponding to the variables in
    // the clause. 
    var abstraction = 0
    for (i <- 0 until lit.length ) {
      abstraction |= 1 << (lit(i).variable & 31)
    }
    abstraction
  }

  def size = lit.length

  // Get the i-th literal 
  def apply(i:Int) = lit(i)
  def update(i:Int, l:Lit) = {
    lit(i) = l
  }
  def indexOf(l: Lit) = lit.indexOf(l)
  def remove(l: Lit) {
    val i = indexOf(l)
    lit(i) = lit.last
    lit = lit.dropRight(1)
  }

  def strengthen(p:Lit) {
    remove(p)
    abst = calcAbstraction
  }

  /** Check if this clause sumsumes the other clause, and at the same
   * time, it can be used to simplify the other by subsumption resolution.
   *
   * Returns :
   *  - Lit.error - No subsumption
   *  - lit.undef - This clause subsumes other
   *  - p - The literal ~p can be deleted from other by strengthening other.
   */  
  def subsumes(other:Clause) = {
    if (other.size < size || 
	(!learnt && !other.learnt && (abst & ~other.abst) !=0))
      Lit.error
    else { 
      var ret = Lit.undef // assume
      var notFound = false // Cannot find either lit or ~lit
      lit.foreach{ thisLit => 
	if (other.lit.contains(thisLit)) {
	} else if (ret == Lit.undef && other.lit.contains(Lit.not(thisLit))) {
	  // First instance of ~thisLit
	  ret = thisLit
	} else {
	  //
	  notFound = true
	}
		}
      // If there are literals lit where neither lit or ~lit were found
      // return error
      if (!notFound) ret else Lit.error
     }
    
  }
}

object Clause {
  def apply(lits: Array[Lit], learnt:Boolean) =
    new Clause(lits, learnt)
}
