package me.zhihan.sat

import org.scalatest.FunSuite 

class HeapTestSuite extends FunSuite {
  test("Heap sort") {
    val keys = Array(1,4,3,2)
    val cmp = (i:Int,j:Int)=> keys(i) - keys(j)
    val heap = new MutableBinaryMinHeap(cmp)
    heap.insert(0)
    heap.insert(1)
    heap.insert(2)
    heap.insert(3)
    
    assert(heap.validate)
    var a = heap.removeMin
    assert(a == 0)
    a = heap.removeMin
    assert(a == 3)
    a = heap.removeMin
    assert(a == 2)
    a = heap.removeMin
    assert(a == 1)
    assert(heap.isEmpty)
  }

  test("Bump ") {
    val keys = Array(1,4,3,2)
    val cmp = (i:Int,j:Int)=> keys(i) - keys(j)
    val heap = new MutableBinaryMinHeap(cmp)
    heap.insert(0)
    heap.insert(1)
    heap.insert(2)
    heap.insert(3)
    
    keys(2) = 5
    heap.update(2)
    assert(heap.validate)

    var a = heap.removeMin
    assert(a == 0)
    a = heap.removeMin
    assert(a == 3)
    a = heap.removeMin
    assert(a == 1)
    a = heap.removeMin
    assert(a == 2)
    assert(heap.isEmpty)
  }

  test("Filter ") {
    val keys = Array(1,4,3,2)
    val cmp = (i:Int,j:Int)=> keys(i) - keys(j)
    val filt = (i:Int) => keys(i) > 2
    val heap = new MutableBinaryMinHeap(cmp)
    heap.insert(0)
    heap.insert(1)
    heap.insert(2)
    heap.insert(3)
    
    heap.filter(filt)

    var a = heap.removeMin
    assert(a == 2)
    a = heap.removeMin
    assert(a == 1)
    assert(heap.isEmpty)
  }

}
