package my.sat

import my.sat._

import scala.collection.mutable.ArrayBuffer

import scala.math.Ordering
import scala.collection.immutable.TreeSet
import scala.util.Sorting 
import scala.collection.mutable.Set
import scala.collection.mutable.Stack

// Pair of (idx, act) sorted by activities
case class Activity(val i:Var.t, val act:Double) 
{}


class Solver {
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
  def abstractLevel(v:Var.t) = { // Abstraction of the levels
    1 << (level(v) & 31)
  }

  // Assignments that forms a "trail"
  // level 0: [ l0 l1 ... l(trail_lim(0) -1) 
  // level 1:   l(trail_lim(0)) .... ]
  val trail = ArrayBuffer[Lit]() 

  // Index into trail to indicate levels
  val trailLim = ArrayBuffer[Int]() 
  
   def newDecisionLevel { trailLim.append(trail.size) }
   def decisionLevel = trailLim.size 

  // Getting values of variable, literal and clause
   def value(v:Var.t):LBool = assigns(v)
   def value(l:Lit):LBool = value(l.variable).xor(l.sign)

   def satisfied(c:Clause):Boolean = 
    c.lit.exists(l => value(l) == LBool.True )

  // Variable ordering
  var varOrder = TreeSet[Activity]() (Ordering.by[Activity,Double](_.act))
   def insertVarOrder(v:Var.t) {
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

  def watchClause(c: Clause) {
    assert(c.size > 1)

    // A clause is always watched by negations of the first two literals
    // When the watch moves, the literals are moved accordingly in the 
    // clause.
    watches((Lit.not(c(0))).toInt).append(c)
    watches((Lit.not(c(1))).toInt).append(c)
  }

  def unwatchClause(c:Clause) {
    assert(c.size > 1)
    watches((Lit.not(c(0))).toInt) -= c
    watches((Lit.not(c(1))).toInt) -= c
  }


   def isLocked(c:Clause):Boolean = {
    // A clause is locked if its first literal is true
    // and the clause is used as a reason for this variable. 
    (reasons(c(0).variable) == c) && (value(c(0)) == LBool.True)
  }

   def removeClause(c:Clause) {
    if (!c.learnt) {
      unwatchClause(c)
    }
  }

  // Cancel the assignments above or equal to trailLim(level)
   def cancelUntil(level:Int) {
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

  private def uncheckedEnqueue(p: Lit, from:Option[Clause]) {
    // assign variable to negation of Lit from and enqueue
    // Assume the value is unknown
    assert(value(p) == LBool.Unknown)
    assigns(p.variable) = LBool(!p.sign)
    level(p.variable) = decisionLevel
    reasons(p.variable) = from
    trail.append(p)
  }

  /* Enqueue a literal and return whether the solver is valid*/
  def enqueue(p: Lit, from:Option[Clause]):Boolean = {
    if (value(p) == LBool.Unknown) {
      uncheckedEnqueue(p, from)
      true
    } else {
      value(p) != LBool.False
    }
  }
  
  private def findNewWatch(clause:Clause) = {
    val falseLit = clause(1)
    // Try to locate a new watch
    var newWatchFound = false
    var k = 2
    while (k < clause.size && !newWatchFound) {
      if (value(clause(k)) != LBool.False) {
	// Swap c(1) with c(k)
	newWatchFound = true
	clause(1) = clause(k)
	clause(k) = falseLit
	
	val lit = Lit.not(clause(1))
	watches(lit.toInt).append(clause)
      } else {
	k+=1
      }
    }
    newWatchFound
  }

  private def moveFirstLiteral(clause:Clause, p:Lit){
    val falseLit = Lit.not(p)
    // Move literals so false lit is in [1]
    if (clause(0) == falseLit ) {
      clause(0) = clause(1)
      clause(1) = falseLit
    }
    assert(clause(1) == falseLit)
  }

  def propagate() = {
    var confl:Option[Clause] = None
    while (qhead < trail.size ) {
      var p = trail(qhead)
      qhead += 1 
      val ws = watches(p.toInt)

      val keepWatch = ArrayBuffer[Clause]()

      for (i <- 0 until ws.size ) {
	val clause = ws(i)
	if (confl.isEmpty) {
	  moveFirstLiteral(clause, p)

	  val first = clause(0)
	  if (value(first) == LBool.True) {
	    // Already satisfied, nothing to do
	    keepWatch.append(clause)
	  } else {
	    val newWatchFound = findNewWatch(clause)
	    if (!newWatchFound) {
	      // Keep watching the clause
	      keepWatch.append(clause)
              
	      if (value(first) == LBool.False) {
		// conflict
		confl = Some(clause)
		qhead = trail.size
	      } else {
		uncheckedEnqueue(first, Some(clause))
	      }
	    }
	  }
	} else {
	  // Already in conflict, keep remaining watches
	  keepWatch.append(clause)
	}
      }
      watches(p.toInt) = keepWatch
    }
    confl
  }

  private def cleanupClause(ps:Array[Lit]) = {
    /* Remove redundancy in the literals
     *   1) False literals are removed
     *   2) Repeated entries are removed
     *   Return true if tautology
     *          false if invalid;
     *          otherwise unknown
     */ 
    
    if (ps.exists(x => value(x) == LBool.True)) {
      (Array[Lit](), LBool.True)
    } else {
      // Sort literals by their indices
      Sorting.quickSort(ps) (Ordering.by[Lit,Int](_.toInt))
      
      // Scan literals
      // remove redundancy and discover contradiction
      val keepLits = ArrayBuffer[Lit]()
      var lastLit = Lit.undef
      var isTautology = false // p || ~p is considered tautology
      for (i <- 0 until ps.size ) {
        if (!isTautology) {
          if (ps(i) == Lit.not(lastLit)) {
            isTautology = true
          } else if (ps(i) != lastLit && value(ps(i)) != LBool.False ) {
            keepLits.append(ps(i))
            lastLit = ps(i)
          } 
        }
      }
      // Return arguments
      if (isTautology) {
        (Array[Lit](), LBool.True)
      } else if (keepLits.isEmpty) {
        (Array[Lit](), LBool.False)
      } else {
        (keepLits.toArray, LBool.Unknown)
      }
    }
  }
  
  def addClause(ps:Array[Lit]) = {
    // Add a clause to the solver 
    // return true if no conflict, false if conflict.
    assert (decisionLevel == 0)
    if (!ok) {
      false
    } else {
      val (lits, status) = cleanupClause(ps)
      if (status == LBool.True) {
        true
      } else if (status == LBool.False) {
        false
      } else {
        // Only process unknown clauses
        if (lits.size == 1) {
          // Unit clause
          assert(value(lits(0)) == LBool.Unknown)
          uncheckedEnqueue(lits(0), None)
          val confl = propagate()
          confl.isEmpty
        } else {
          val clause = Clause(lits, false)
          clauses.append(clause)
          watchClause(clause)
          true
        }
      }
    }
  }
  
  def analyze(confl:Option[Clause]) = {
    var pathCount = 0
    var thisLit = Lit.undef
    
    val learnt = ArrayBuffer(thisLit) // leave room for first
    var idx = trail.size - 1 
    // "seen" serves as a work-list
    val seen = Set[Var.t]()

    var clause:Option[Clause] = confl

    while (thisLit == Lit.undef || // initial 
	   pathCount >0 ) {
      // bump activity XXX
      assert(!clause.isEmpty)
      val c = clause.get
      val firstLitIdx = if (thisLit==Lit.undef) 0 else 1
      for (j <- firstLitIdx until c.size) {
	val q = c(j)
	val v = q.variable
	if (!seen.contains(v) && level(v) >0) {
	  // bump activity
	  seen += v
	  if (level(v) >= decisionLevel) {
	    // Increase path count
	    pathCount += 1
	  } else {
	    learnt.append(q)
	  }
	}
      }
      while(!seen.contains(trail(idx).variable)) {
	// follow the trail until find an seen variable
	idx -= 1
      }
      thisLit = trail(idx)
      clause = reasons(thisLit.variable)
      // When looking at reasons of this literal, it is removed
      // from the worklist
      seen.remove(thisLit.variable)
      pathCount -= 1
    }
    // When stop, thisLit is an UIP
    learnt(0) = Lit.not(thisLit)
    // Here, seen contains all active literals except intermediate
    // literals. The UIP is not in the seen list.

    /* Only implement the 'expensive' alternative of clause minimization */
    
    val abstractLevels = computeAbstractLevels(learnt)
    
    val minLearnt = ArrayBuffer[Lit](learnt(0)) // Initialize the UIP
    for ( i<- 1 until learnt.size) {  // Skip UIP
      val l = learnt(i)
      reasons(l.variable) match {
        case None => minLearnt.append(l) // No reason, decision literals
        case Some(r) => 
          // Has reason, need to check its reasons
          if (!litRedundant(l, abstractLevels, seen)) {
            minLearnt.append(l)
          }
      }
                  }
    val btLevel = computeBTLevel(minLearnt)
    (minLearnt, btLevel)
  }

  def computeAbstractLevels(ls:ArrayBuffer[Lit]) = {
    var levels = 0
    for( i <- 1 until ls.size) {
      val l = ls(i)
      val lv = abstractLevel(l.variable)
      levels = levels | lv          
    }
    levels
  }

  /* Minimization of conflict clause using self subsumption
   *
   * See "MiniSAT - A SAT solver with conflict clause minimization" SAT 2005 
   * */
  def litRedundant(p:Lit, abstractLevels: Int, seen:Set[Var.t]) = {
    val analyzeStack = Stack[Lit](p)
    val lseen = Set[Var.t]() ++ seen // Local set of seen literals
    var isRedundant = true // Assume
    while (!analyzeStack.isEmpty && isRedundant) { // DFS
      val q = analyzeStack.pop
      assert(!reasons(p.variable).isEmpty)
      val reason = reasons(p.variable).get 
      for (i <- 1 until reason.size 
           if isRedundant ) { // Skipping the asserting literal
        val p = reason(i) 
        // If any literals in the reason is not found in the original
        // clause (seen), the literal is not redundant.
        val px = p.variable
        if (!lseen.contains(px) && level(px) >0) {
          // new reason
          if ( !reasons(px).isEmpty && ((abstractLevel(px) & abstractLevels)!=0)) {
            lseen += px // px is seen in this function 
            analyzeStack.push(p) // Need to investigate p
          } else {
            // the new reason is either at a different level or
            // a decision variable
            isRedundant  = false
          }
        } // If this is an old reason or assumption, goto next reason
      }
    }
    isRedundant
  }

  def computeBTLevel(learnt:ArrayBuffer[Lit]) = {
    // learnt will be altered in this function since it is mutable
    if (learnt.size == 1) {
      0
    } else {
      var maxI = 1
      for (i <- 2 until learnt.size) {
        if (level(learnt(i).variable) > level(learnt(maxI).variable)) {
          maxI = i
        }
      }
      // Move the literal with max level to the first variable so it will
      // be used to watch the conflict clause
      val p = learnt(maxI)
      learnt(maxI) = learnt(1)
      learnt(1) = p
      level(p.variable)
    }
  }
}
