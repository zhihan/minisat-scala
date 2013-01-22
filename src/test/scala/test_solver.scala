package test.sat

import my.sat._

import org.scalatest.FunSuite 

class SolverTestSuite extends FunSuite {
  test("Init") {
    val a = Solver.newVar(true)
    val b = Solver.newVar(false)
    assert(Solver.nVars == 2)
  }
}
