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
}
