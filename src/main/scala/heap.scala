package my.sat

import scala.collection.mutable.ArrayBuffer

/** A Binary min heap used for managing activities */
class MutableBinaryMinHeap(val comp:(Int,Int)=>Int) {

  // Heap is a sorted list of integers [0 ... N] and indices
  // is a list of the inices of the integers in the heap, if the number
  // is not in heap, indices(i) == -1
  val heap = ArrayBuffer[Int]()  
  val indices = ArrayBuffer[Int]()  // indices(heap(i)) == i
  
  // Heap indices must be prefixed by 'heap'
  private def left(heapIdx:Int) = heapIdx*2 + 1
  private def right(heapIdx:Int) = heapIdx*2 + 2
  private def parent(heapIdx:Int) = (heapIdx-1) >> 1


  private def lt(i:Int, j:Int) = comp(i,j) < 0
  def size = heap.size
  def isEmpty = heap.isEmpty
  
  def inHeap(i: Int) = (i < indices.size) && (indices(i) >= 0)  
  private def decrease(i:Int) = percolateUp(indices(i))
  private def increase(i:Int) = percolateDown(indices(i))

  private def percolateUp(heapIdx:Int) {
    var x = heap(heapIdx)
    var hI = heapIdx
    while (hI != 0 && lt(x, heap(parent(hI)))) {
      // If x < parent, move parent down 
      heap(hI) = heap(parent(hI))
      indices(heap(hI)) = hI
      hI = parent(hI)
    }
    heap(hI) = x
    indices(x) = hI
  }
  
  private def percolateDown(heapIdx:Int) {
    var x = heap(heapIdx)
    var hI = heapIdx
    var stop = false
    while (left(hI) < heap.size && !stop) {
      val child = if (right(hI) < heap.size && lt(heap(right(hI)), heap(left(hI)))) {
	right(hI)
      } else {
	left(hI)
      }
      if (!lt(heap(child), x)) {
	stop = true // break
      } else {
	// Move child to hI and move hI to child
	heap(hI) = heap(child)
	indices(heap(hI)) = hI
	hI = child
      }
    }
    heap(hI) = x
    indices(x) = hI
  }
 
  
  def validate() = {
    def heapProp(heapIdx:Int) = {
      assert(heapIdx < heap.size)
      if (heapIdx==0) true else !lt(heap(heapIdx), heap(parent(heapIdx))) 
    }

    indices.forall(hI => 
      if (hI >= 0) { 
	heapProp(hI)
      } else {
	true
      })
  }
  
  def insert(n: Int) {
    val sz = indices.size
    for (i <- sz to n) {
      // Grow indices to n+1
      indices.append(-1)
    }

    indices(n) = heap.size
    heap.append(n)
    percolateUp(indices(n))
  }

  def clear {
    indices.clear
    heap.clear
  }
  
  def removeMin() = {
    // Remove x 
    val x = heap(0)
    indices(x) = -1 
    // Insert last entry
    heap(0) = heap.last
    indices(heap(0)) = 0
    if (heap.size > 1) {
      heap.remove(heap.size-1)
      // Update
    } else {
      heap.clear
    }
    if (heap.size > 1) {
      percolateDown(0)
    }
    x
  }

  def update(n:Int) {
    if (!inHeap(n)) {
      insert(n)
    } else {
      percolateUp(indices(n))
      percolateDown(indices(n))
    }
  }

  def filter(filt:(Int)=>Boolean) {
    val old = heap.toArray
    heap.clear
    // Re-populate heap
    old.foreach( i =>
      if (filt(i)) {
	// keep
	heap.append(i)
	indices(i) = heap.size-1
      } else {
	indices(i) = -1
      })
    // Sort
    for (i <- heap.size/2-1 to 0 by -1) {
      percolateDown(i)
    }
    assert(validate)

  }
  
}
