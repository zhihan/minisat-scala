package test.sat

import my.sat._

import org.scalatest.FunSuite 

class SolverTestSuite extends FunSuite {
  test("Init") {
    val s = new Solver()
    val a = s.newVar(true)
    val b = s.newVar(false)
    assert(s.nVars == 2)
  }

  test("Enqueue") {
    val s = new Solver()
    val a = s.newVar(true)
    val la = Lit(a, false)
    s.enqueue(la, None)
    assert(s.value(la) == LBool.True)
    assert(s.value(a) == LBool.True)
  }

  test("Preprocessing satisfied clause") {
    val s = new Solver()
    val a = s.newVar(true)
    val la = Lit(a, false)
    s.enqueue(la, None) // Set a to True
    val r = s.addClause(Array(la))
    assert(r == true)  //already satisfied
    assert(s.clauses.isEmpty)
  }

  test("Preprocessing falsified clause") {
    val s = new Solver()
    val a = s.newVar(true)
    val r1 = s.addClause(Array(Lit(a,false))) // set a to true
    val r = s.addClause(Array(Lit(a,true)))
    assert(r == false)  //already falsified
    assert(s.clauses.isEmpty)
  }

  test("Preprocessing tautology") {
    val s = new Solver()
    val a = s.newVar(true)
    val l1 = Lit(a, false)
    val l2 = Lit(a, true)
    val r = s.addClause(Array(l1,l2)) 
    assert(r == true)  //tautology
    assert(s.clauses.isEmpty)
  }

  test("Preprocessing unit clause") {
    val s = new Solver()
    val a = s.newVar(true)
    val l1 = Lit(a, false)
    val r = s.addClause(Array(l1,l1)) //repeating
    assert(r == true)
    assert(s.value(a) == LBool.True) 
    assert(s.clauses.isEmpty)    
  }

  test("Preprocessing propagation") {
    val s = new Solver()
    val a = s.newVar(true)
    val b = s.newVar(true)
    val c = s.newVar(true)
    
    val r1 = s.addClause(Array(Lit(b, true), Lit(c,false))) // b -> c
    val r2 = s.addClause(Array(Lit(a, true), Lit(b,false))) // a -> b
    val r3 = s.addClause(Array(Lit(a, false))) // a

    assert(r3 == true)
    assert(s.value(c) == LBool.True)
    assert(s.value(b) == LBool.True)
    assert(s.clauses.size == 2)
  }

  test("Preprocessing conflict") {
    val s = new Solver()
    val a = s.newVar(true)
    val b = s.newVar(true)
    val r1 = s.addClause(Array(Lit(a, true), Lit(b, true))) // !a  !b
    val r2 = s.addClause(Array(Lit(a, true), Lit(b, false))) // a -> b
    val r = s.addClause(Array(Lit(a, false))) // a
    assert(r == false)
  }

  test("Conflict resolution") {
    val s = new Solver()
    val a = s.newVar(true)
    val b = s.newVar(true)
    val c = s.newVar(true)
    val d = s.newVar(true)
    val e = s.newVar(true)
    val f = s.newVar(true)
    s.addClause(Array(Lit(a,true), Lit(d,true), Lit(b,false)))
    s.addClause(Array(Lit(d,true), Lit(f,true), Lit(e,false)))
    s.addClause(Array(Lit(b,true), Lit(e,true), Lit(c,false)))
    s.addClause(Array(Lit(c,true)))
    
    // enter decision
    s.newDecisionLevel
    s.enqueue(Lit(a, false), None)
    s.propagate

    s.newDecisionLevel
    s.enqueue(Lit(f, false), None)
    s.propagate

    s.newDecisionLevel
    s.enqueue(Lit(d, false), None)
    val confl = s.propagate()

    val (res,btlevel) = s.analyze(confl)
    assert(res.size == 3)
    assert(btlevel == 2)
    //println(res)

  }
}
