package test.sat

import my.sat._

import org.scalatest.FunSuite 

class TypeTestSuite extends FunSuite {
  test("Var") {
    val a = Var(1)
    assert( a == 1)
    assert( Var.toInt(a) == 1)
  }

  test("Lit") {
    val a = Var(1)
    val al = Lit(a, true)
    val af = Lit(a, false)
    assert(al.toInt == Var.toInt(a)*2 +1)
    assert(af.toInt == Var.toInt(a)*2)
  }

  test("Clause") {
    val a = Var(0)
    val b = Var(2)
    val lits = Array(Lit(a,true), Lit(b,false))
    val cl = new Clause(lits, false)
    assert(cl.abst == 5)  // Abstraction

    cl.strengthen(Lit(a,true))
    assert(cl.size == 1)
    assert(cl.abst == 4)

    val clause1 = Clause(Array(Lit(0, true)), true)
    val clause2 = Clause(Array(Lit(0, true), Lit(1,true)), true)
    
    // 
    assert(clause1.subsumes(clause1) == Lit.undef)
    assert(clause1.subsumes(clause2) == Lit.undef)
    assert(clause2.subsumes(clause1) == Lit.error)

    val clause3 = Clause(Array(Lit(0,false), Lit(1,true)), true)
    assert(clause1.subsumes(clause3) == Lit(0,true))
  }
}
