type T = int
class {:autocontracts} PriorityQueue {
  var heap : array <T>
  var size : nat
  ghost const capacity: nat
  ghost var elems: multiset<T>

  function getLen(): nat
  {
    heap.Length
  }

  ghost predicate Valid ()
  {
    0 <= size <= heap.Length &&
    capacity == heap.Length &&
    elems == multiset(heap[..size]) &&
    isMaxHeap()
  }

  ghost predicate {:autocontracts false} isMaxHeap()
    reads this, heap
  {
    size <= heap.Length && forall i :: 1 <= i < size ==> heap [i] <= heap [(i - 1) / 2]
  }

  constructor(cap : nat)
    ensures isEmpty()
  {
    heap := new T[cap];
    size := 0;

    capacity := cap;
    elems := multiset{};
  }

  predicate isEmpty() { size == 0 }

  predicate isFull()
    ensures isFull() <==> size == capacity
  {
    size == heap.Length
  }

  // /* Uncomment here and line 91, to comment out insert (to make verification faster)

  predicate {:autocontracts false} heapifyUpInv (k : nat)
    reads this, heap
  {
    size <= heap.Length

    // forall nodes except k, the maxheap property holds
    && (forall i :: 1 <= i < size && i != k ==> heap [i] <= heap [(i - 1) / 2])

    // special case for k, any node whose parent is k must be less than or equal to its grandparent
    && (k > 0 ==> (forall i :: 1 <= i < size && (i - 1) / 2 == k ==> heap [i] <= heap [((i - 1) / 2 - 1) / 2]))
  }

  method insert(x : T)
    requires !isFull()
    ensures elems == old(elems) + multiset{x}
    ensures size == old(size) + 1
  {
    assert size < heap.Length;
    heap[size] := x;
    size := size + 1;

    elems := multiset(heap[..size]);
    heapifyUp();
  }

  method {:autocontracts false} heapifyUp()
    requires size > 0
    requires heapifyUpInv(size - 1)
    modifies heap
    ensures isMaxHeap()
    ensures multiset(heap[..size]) == old(multiset(heap[..size]))
  {
    var k := size - 1;

    while k > 0 && heap [k] > heap [(k - 1) / 2]
      decreases k
      invariant 0 <= k < size
      invariant multiset(heap[..size]) == old(multiset(heap[..size]))
      invariant heapifyUpInv(k)
    {
      heap [k], heap [(k - 1) / 2] := heap [(k - 1) / 2], heap [k];
      k := (k - 1) / 2;
    }
  }

  // */

  // /* Uncomment here and line 91, to comment out delete (this takes forever to verify)
  predicate isMax(x : T, s : multiset <T>)
  {
    x in s &&
    forall k :: k in s ==> x >= k
  }

  predicate {:autocontracts false } heapifyDownInv (k : nat)
    reads this, heap
  {
    size <= heap.Length

    // for all nodes whose parent is not k, the maxheap property holds
    && (forall i :: 1 <= i < size && (i - 1) / 2 != k ==> heap [i] <= heap [(i - 1) / 2])

    // for positive k's, any node i whose parent is k must be less than or equal to its grandparent
    // special case of the heapifyDown operation, as node k might temporarily violate the heap properties
    // as it descends down the tree
    && (k > 0 ==> forall i :: 1 <= i < size && (i - 1) / 2 == k ==> heap [i] <= heap [((i - 1) / 2 - 1) / 2])
  }

  method deleteMax() returns (x : T)
    requires !isEmpty()
    ensures isMax(x, old(elems))
    ensures elems == old(elems) - multiset{x}
  {
    maxIsAtTop();
    x := heap [0];
    size := size - 1;
    if size > 0 {
      heap[0] := heap[size];
      heapifyDown();
    }
    elems := multiset(heap[..size]);
  }

  method {:autocontracts false} heapifyDown()
    requires size > 0
    requires heapifyDownInv(0)
    modifies heap
    ensures isMaxHeap()
    ensures multiset(heap[..size]) == old(multiset(heap[..size]))
  {
    var k := 0;

    while true
      decreases size - k
      invariant 0 <= k < size
      invariant multiset(heap[..size]) == old(multiset (heap[..size]))
      invariant heapifyDownInv(k)
    {
      var leftChild := 2 * k + 1;
      var rightChild := 2 * k + 2;

      if leftChild >= size { return; }

      var maxChild := if rightChild < size && heap[rightChild] > heap[leftChild]
      then rightChild else leftChild;

      if heap [k] > heap[maxChild] { return; }

      heap [k], heap[maxChild] := heap[maxChild], heap[k];
      k := maxChild;
    }
  }

  // */

  lemma maxIsAtTopHelper(n: nat)
    requires n <= size
    ensures forall i :: 0 <= i < n ==> heap[i] <= heap[0]
  {
    if n == 0 {
      return;
    }

    if n > 1 {
      maxIsAtTopHelper(n-1);
    }
  }

  // this proof is easy by induction, we discharge the proof to another
  // lemma that is indexed by a number, essentially descending on the size of the heap
  lemma maxIsAtTop ()
    ensures forall i :: 0 <= i < size ==> heap[i] <= heap[0]
  {
    if size == 0 { return; }
    maxIsAtTopHelper(size);
  }
}

method testPriorityQueue()
{
  var h := new PriorityQueue(10);
  assert h.size == 0;
  assert h.isEmpty();
  assert h.getLen() == 10; // for some reason this fails, and the rest of the code relies on this...
  assert !h.isFull();

  h.insert(2);
  assert h.size == 1;
  assert !h.isFull();

  h.insert(5);
  assert h.size == 2;
  assert !h.isFull();

  h.insert(1);
  assert h.size == 3;
  assert !h.isFull();

  h.insert(1);
  assert h.size == 4;
  assert !h.isFull();

  var x := h.deleteMax();
  assert x == 5;
  x := h.deleteMax();
  assert x == 2;
  x := h.deleteMax();
  assert x == 1;
  x := h.deleteMax();
  assert x == 1;
  assert h.isEmpty();
}

