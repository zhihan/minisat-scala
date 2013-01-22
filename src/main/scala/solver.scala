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

  // Per variable data
  val activity = ArrayBuffer[Double]() // one per variable
  val assigns = ArrayBuffer[LBool] () // one per variable
  val decisionVar = ArrayBuffer[Boolean]() // 

  // Variable ordering
  var varOrder = TreeSet[Activity]() (Ordering.by[Activity,Double](_.act))
  def insertVarOrder(v:Var.t) {
    val act = activity(v)
    val a = Activity(v, act)
    if (!varOrder.contains(a) && decisionVar(v)) {
      varOrder = varOrder + a // Insert
    }
  }
}