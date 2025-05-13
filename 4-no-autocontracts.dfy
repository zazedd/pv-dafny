type T = int
class PriorityQueue {
  var heap: array<T>
  var size: nat
  ghost const capacity: nat
  ghost var elems: multiset<T>

  ghost var Repr: set<object?>

  function getLen(): nat
    requires Valid()
    reads Repr
  {
    heap.Length
  }

  ghost predicate Valid()
    reads this, Repr
    ensures Valid() ==> this in Repr
  {
    this in Repr &&
    null !in Repr &&
    heap in Repr &&
    0 <= size <= heap.Length &&
    capacity == heap.Length &&
    elems == multiset(heap[..size]) &&
    isMaxHeap()
  }

  ghost predicate isMaxHeap()
    reads this, heap
  {
    size <= heap.Length &&
    forall i : int  :: 1 <= i < size ==> heap[i] <= heap[(i - 1) / 2]
  }

  constructor (cap: nat)
    ensures Valid()
    ensures fresh(Repr)
    ensures isEmpty()
  {
    heap := new T[cap];
    size := 0;
    capacity := cap;
    elems := multiset{};

    new;
    Repr := {this};
    if !(heap in Repr) {
      Repr := Repr + {heap};
    }
  }

  predicate isEmpty()
    requires Valid()
    reads Repr
  {
    size == 0
  }

  predicate isFull()
    requires Valid()
    reads Repr
    ensures isFull() <==> size == capacity
  {
    size == heap.Length
  }

  predicate heapifyUpInv(k: nat)
    reads this, heap
  {
    size <= heap.Length &&
    (forall i: int {:trigger heap[i]} :: 1 <= i < size && i != k ==> heap[i] <= heap[(i - 1) / 2]) &&
    (k > 0 ==> forall i: int {:trigger heap[i]} :: 1 <= i < size && (i - 1) / 2 == k ==> heap[i] <= heap[((i - 1) / 2 - 1) / 2])
  }

  method insert(x: T)
    requires Valid()
    requires !isFull()
    modifies Repr
    ensures Valid()
    ensures fresh(Repr - old(Repr))
    ensures elems == old(elems) + multiset{x}
    ensures size == old(size) + 1
  {
    assert size < heap.Length;
    heap[size] := x;
    size := size + 1;
    elems := multiset(heap[..size]);
    heapifyUp();

    if !(heap in Repr) {
      Repr := Repr + {heap};
    }
  }

  method heapifyUp()
    requires size > 0
    requires heapifyUpInv(size - 1)
    modifies heap
    ensures isMaxHeap()
    ensures multiset(heap[..size]) == old(multiset(heap[..size]))
  {
    var k: int := size - 1;
    while k > 0 && heap[k] > heap[(k - 1) / 2]
      decreases k
      invariant 0 <= k < size
      invariant multiset(heap[..size]) == old(multiset(heap[..size]))
      invariant heapifyUpInv(k)
    {
      heap[k], heap[(k - 1) / 2] := heap[(k - 1) / 2], heap[k];
      k := (k - 1) / 2;
    }
  }

  predicate isMax(x: T, s: multiset<T>)
    requires Valid()
    reads Repr
  {
    x in s &&
    forall k: int {:trigger s[k]} :: k in s ==> x >= k
  }

  predicate heapifyDownInv(k: nat)
    reads this, heap
  {
    size <= heap.Length &&
    (forall i: int {:trigger heap[i]} :: 1 <= i < size && (i - 1) / 2 != k ==> heap[i] <= heap[(i - 1) / 2]) &&
    (k > 0 ==> forall i: int {:trigger heap[i]} :: 1 <= i < size && (i - 1) / 2 == k ==> heap[i] <= heap[((i - 1) / 2 - 1) / 2])
  }

  method deleteMax() returns (x: T)
    requires Valid()
    requires !isEmpty()
    modifies Repr
    ensures Valid()
    ensures fresh(Repr - old(Repr))
    ensures isMax(x, old(elems))
    ensures elems == old(elems) - multiset{x}
  {
    maxIsAtTop();
    x := heap[0];
    size := size - 1;
    if size > 0 {
      heap[0] := heap[size];
      heapifyDown();
    }
    elems := multiset(heap[..size]);

    if !(heap in Repr) {
      Repr := Repr + {heap};
    }
  }

  method heapifyDown()
    requires size > 0
    requires heapifyDownInv(0)
    modifies heap
    ensures isMaxHeap()
    ensures multiset(heap[..size]) == old(multiset(heap[..size]))
  {
    var k: int := 0;
    while true
      invariant 0 <= k < size
      invariant multiset(heap[..size]) == old(multiset(heap[..size]))
      invariant heapifyDownInv(k)
      decreases size - k
    {
      var leftChild: int := 2 * k + 1;
      var rightChild: int := 2 * k + 2;
      if leftChild >= size {
        return;
      }
      var maxChild: int := if rightChild < size && heap[rightChild] > heap[leftChild] then rightChild else leftChild;
      if heap[k] > heap[maxChild] {
        return;
      }
      heap[k], heap[maxChild] := heap[maxChild], heap[k];
      k := maxChild;
    }
  }

  lemma maxIsAtTopHelper(n: nat)
    requires Valid()
    requires n <= size
    ensures forall i: int {:trigger heap[i]} :: 0 <= i < n ==> heap[i] <= heap[0]
  {
    if n == 0 {
      return;
    }
    if n > 1 {
      maxIsAtTopHelper(n - 1);
    }
  }

  lemma maxIsAtTop()
    requires Valid()
    ensures forall i: int {:trigger heap[i]} :: 0 <= i < size ==> heap[i] <= heap[0]
  {
    if size == 0 {
      return;
    }
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

