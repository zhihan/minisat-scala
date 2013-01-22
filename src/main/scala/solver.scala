package my.sat

import my.sat._

import scala.collection.mutable.ArrayBuffer

import scala.math.Ordering
import scala.collection.immutable.TreeSet

// Pair of (idx, act) sorted by activities
case class Activity(val i:Var.t, val act:Double) 
{}




object Solver {
  // Constructor
  var ok = true

  var qhead = 0 // Index into trail to indicate head of queue
  
  // Number of top-level assigns since last call to simplify
  var simpDBNumAssigns = -1 
  // Remaining number of propagations that must be made before
  // next execution of simplify
  var simpDBNumProps = 0

  var progressEstimate = 0.0 // Set by search

  // Constants
  val varDecay = 1/0.95
  val clauseDecay = 1/0.999
  val randomVarFreq = 0.02
  val restartFirst = 100
  val restartInc = 1.5
  val learntSizeFactor = 1.0/3.0
  val learntSizeInc = 1.1
  
  val clauseInc = 1
  val varInc = 1

  // Mutable members

  // watches maps a literal to a list of clauses
  val watches = ArrayBuffer[ArrayBuffer[Clause]]()
  val clauses = ArrayBuffer[Clause]()
  val learnts = ArrayBuffer[Clause]()

  // Per-variable data
  val activity = ArrayBuffer[Double]() 
  val assigns = ArrayBuffer[LBool] ()  // assigned value
  val decisionVar = ArrayBuffer[Boolean]() // whether the variable is decision candidate
  val reasons = ArrayBuffer[Option[Clause]]()
  val level = ArrayBuffer[Int]()

  // Assignments that forms a "trail"
  // level 0: [ l0 l1 ... l(trail_lim(0) -1) 
  // level 1:   l(trail_lim(0)) .... ]
  val trail = ArrayBuffer[Lit]() 

  // Index into trail to indicate levels
  val trailLim = ArrayBuffer[Int]() 
  
  private def newDecisionLevel { trailLim.append(trail.size) }
  private def decisionLevel = trailLim.size 

  // Getting values of variable, literal and clause
  private def value(v:Var.t):LBool = assigns(v)
  private def value(l:Lit):LBool = value(l.toInt).litValue(l.sign)

  private def satisfied(c:Clause):Boolean = 
    c.lit.exists(l => value(l) == LBool.True )

  // Variable ordering
  var varOrder = TreeSet[Activity]() (Ordering.by[Activity,Double](_.act))
  private def insertVarOrder(v:Var.t) {
    val act = activity(v)
    val a = Activity(v, act)
    if (!varOrder.contains(a) && decisionVar(v)) {
      varOrder = varOrder + a // Insert
    }
  }

  def nVars = assigns.size

  // Main methods

  def newVar(isDecision:Boolean):Var.t =  {
    val newV = nVars // New variable

    watches.append(ArrayBuffer[Clause]()) // negative watch
    watches.append(ArrayBuffer[Clause]()) // positive watch
    
    assigns.append(LBool.Unknown) 
    activity.append(0.0)
    level.append(-1) // Not decided
    
    reasons.append(None)  // No reason

    decisionVar.append(isDecision)
    insertVarOrder(newV)

    newV
  }

  def disp = {
    "Variables: " + nVars + "\n" +
    "Clauses: " + clauses.size 
  }

  private def watchClause(c: Clause) {
    assert(c.size > 1)

    // A clause is always watched by negations of the first two literals
    // When the watch moves, the literals are moved accordingly in the 
    // clause.
    watches((Lit.not(c(0))).toInt).append(c)
    watches((Lit.not(c(1))).toInt).append(c)
  }

  private def unwatchClause(c:Clause) {
    assert(c.size > 1)
    watches((Lit.not(c(0))).toInt) -= c
    watches((Lit.not(c(1))).toInt) -= c
  }


  private def isLocked(c:Clause):Boolean = {
    // A clause is locked if its first literal is true
    // and the clause is used as a reason for this variable. 
    (reasons(c(0).variable) == c) && (value(c(0)) == LBool.True)
  }

  private def removeClause(c:Clause) {
    if (!c.learnt) {
      unwatchClause(c)
    }
  }

  // Cancel the assignments above or equal to trailLim(level)
  private def cancelUntil(level:Int) {
    if (decisionLevel > level) {
      // Cancel all assignments on the trail
      for (c <- trail.size-1 to trailLim(level) by -1) {
        val x = trail(c).variable
        assigns(x) = LBool.Unknown
        insertVarOrder(x) // Insert into the ordered list
      }
      qhead = trailLim(level) // queue is empty
      trail.remove(trailLim(level),  trail.size-trailLim(level))
      trailLim.remove(level, decisionLevel - level)
     }
  }
  

}
