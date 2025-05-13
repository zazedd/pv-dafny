// map function over an array. checks which elements are larger than a given x, substitutes those by their multiplication with x
// return the amount of values bigger than x

method mapmult(arr: array?<int>, x: int) returns (count: nat)
  requires arr != null
  modifies arr

  // if a value at a given position in the array is:
  // - bigger than the given x, becomes itself times x
  // - smaller or equal than the given x, stays the same
  ensures forall i :: 0 <= i < arr.Length ==>
                        (old(arr[i]) > x ==> arr[i] == old(arr[i]) * x) &&
                        (old(arr[i]) <= x ==> arr[i] == old(arr[i]))

  // the return value, count, will be exactly the number of values bigger than x in the
  // starting array
  ensures count == | (set i | 0 <= i < arr.Length && old(arr[i]) > x) |
{
  count := 0;
  var i := 0;

  while (i < arr.Length)
    decreases arr.Length - i

    // only valid indices
    invariant 0 <= i <= arr.Length

    // dafny is not smart enough to prove this by itself, so we need the asserts
    // inside the if and else blocks
    invariant count == | (set j | 0 <= j < i && old(arr[j]) > x) |

    // the invariant is the same as the post condition, up until i (the current iterator)
    invariant forall j :: 0 <= j < i ==>
                            (old(arr[j]) > x ==> arr[j] == old(arr[j]) * x) &&
                            (old(arr[j]) <= x ==> arr[j] == old(arr[j]))

    // all of the other positions are still unchanged
    invariant forall j :: i <= j < arr.Length ==> arr[j] == old(arr[j])
  {
    if (arr[i] > x) {
      // proving to dafny that:
      // - the new set will include j = i
      // - so the count will increase by exactly 1
      assert old(arr[i]) > x;
      assert 0 <= i < arr.Length;
      assert (set j | 0 <= j < i + 1 && old(arr[j]) > x) == (set j | 0 <= j < i && old(arr[j]) > x) + {i};

      count := count + 1;
      arr[i] := arr[i] * x;
    } else {
      // here the set doesn't change because arr[i] is not > x
      assert old(arr[i]) <= x;
      assert (set j | 0 <= j < i + 1 && old(arr[j]) > x) == (set j | 0 <= j < i && old(arr[j]) > x);
    }

    i := i + 1;
  }
}
