function max(a : int, b : int) : int {
  if (a < b) then b else a
}

function abs(a : int) : int {
  if (a < 0) then -a else a
}

datatype AVL = Leaf | Node(left:AVL, height: nat, key:int, right:AVL)

function height(t : AVL) : int {
  match t
  case Leaf => 0
  case Node(l, h, _, r) => h
}

function treetoset(t: AVL): set<int>
  decreases t
{
  match t
  case Leaf => {}
  case Node(l, _, x, r) => {x} + treetoset(l) + treetoset(r)
}

function search(x : int, t : AVL) : (res: bool)
  ensures res == (x in treetoset(t))
  decreases t
{
  match t
  case Leaf => false
  case Node(l, _, k, r) => k == x || search(x, l) || search(x, r)
}

ghost predicate isAVL(t : AVL)
  decreases t
{
  match t
  case Leaf => true
  case Node(l, h, x, r) => 
    h == height(t) && isAVL(l) && isAVL(r)
    && -1 <= height(l) - height(r) <= 1 &&
    (forall z :: z in treetoset(l) ==> z < x)
    && (forall z :: z in treetoset(r) ==> z > x)
}

// added {:axiom} so that the compiler didn't complain about the ensures clauses in a bodyless function

// e)
/*
  The preconditions:
  - 1: the first precodition ensures all elements of the left subtree are smaller than root value x
      and that all elements of the right subtree are bigger than root value x
  - 2: the second precondition ensures that both the right and left subtrees are valid AVL trees
  - 3: the third precondition ensures that the height difference between the left and right subtrees is, atmost, 2

  The postconditions:
  - 1: ensures that the resulting tree is a valid AVL tree, and not empty
  - 2: ensures that the height of the resulting tree is either the same as the taller input
      subtree, or, at most, 1 higher
  - 3: ensures that the element set of the resulting tree is equal to the union of the left and right subtrees, and the root value x

  These are all the classic conditions for an AVL tree to be balanced, and it seems to me that it is correct,
  especially because it preserves the binary search tree properties, the height balancing factors and the preservation of the elements.
*/
function {:axiom} equil(l : AVL, x : int, r : AVL) : AVL
  requires (forall z :: z in treetoset(l) ==> z< x) && (forall z :: z in treetoset(r) ==> z > x)
  requires isAVL(l) && isAVL(r)
  requires abs(height(l) - height(r)) <= 2
  ensures isAVL(equil(l,x,r)) && equil(l,x,r) != Leaf
  ensures max(height(l), height(r)) <= height(equil(l,x,r)) <= max(height(l), height(r)) + 1
  ensures treetoset(equil(l,x,r)) == treetoset(l) + treetoset(r) + {x}

function size(t : AVL) : nat
  decreases t
{
  match t
  case Leaf => 0
  case Node(l, _, _, r) => 1 + size(l) + size(r)
}

method insert(x: int, t: AVL) returns (res: AVL)
  requires isAVL(t)
  ensures isAVL(res)
  ensures treetoset(res) == treetoset(t) + {x}
  ensures height(res) <= height(t) + 1
  decreases size(t)
{
  match t
  case Leaf => 
    res := Node(Leaf, 1, x, Leaf);
    assert height(res) == 1; 
  case Node(l, h, k, r) =>
    if x < k {
      var new_left := insert(x, l);

      res := Node(new_left, 1 + max(height(new_left), height(r)), k, r);

      var hl := height(res.left);
      var hr := height(res.right);

      if abs(hl - hr) > 1 {
        res := equil(res.left, res.key, res.right);
      }
    } else if x > k {
      var new_right := insert(x, r);
      res := Node(l, 1 + max(height(l), height(new_right)), k, new_right);

      var hl := height(res.left);
      var hr := height(res.right);

      if abs(hl - hr) > 1 {
        res := equil(res.left, res.key, res.right);
      }
    } else {
      res := t;
    }
    assert height(res) <= height(t) + 1;  // Provide a hint to verifier
}


function update_height(l: AVL, x: int, r: AVL): AVL
{
  Node(l, 1 + max(height(l), height(r)), x, r)
}

function {:axiom} deleteMin(t : AVL) : (res : (int, AVL))
  decreases t
  requires isAVL(t) && t != Leaf
  ensures isAVL(res.1)
  ensures res.0 in treetoset(t)
  ensures forall z :: (z in treetoset(t) ==> res.0 <= z)
  ensures treetoset(t) - {res.0} == treetoset(res.1)
  ensures 0 <= (height(t) - height(res.1)) <= 1

function delete(x : int, t : AVL) : (res : AVL)
  decreases t
  requires isAVL(t)
  ensures isAVL(res)
  ensures treetoset(res) == treetoset(t) - {x}
{
  match t
  case Leaf => Leaf
  case Node(l, _, k, r) =>
    // deleting current node
    if x == k then
      match (l, r)
      case (Leaf, Leaf) => Leaf
      case (Node(_, _, _, _), Leaf) => l
      case (Leaf, Node(_, _, _, _)) => r
      case (Node(_, _, _, _), Node(_, _, _, _)) =>
        var (min_val, new_right) := deleteMin(r);
        var new_tree := update_height(l, min_val, new_right);

        // check if rebalancing is needed
        var hl := height(new_tree.left);
        var hr := height(new_tree.right);

        match new_tree
        case Leaf => Leaf
        case Node(l1, _, key, r1) =>
          if abs(hl - hr) <= 1 then
            new_tree
          else
            equil(l1, key, r1)

    // delete on the left
    else if x < k then
      var new_left := delete(x, l);
      var new_tree := update_height(new_left, k, r);

      var hl := height(new_tree.left);
      var hr := height(new_tree.right);

      match new_tree
      case Leaf => Leaf
      case Node(l1, _, key, r1) =>
        if abs(hl - hr) <= 1 then
          new_tree
        else
          equil(l1, key, r1)

    // delete on the right
    else
      var new_left := delete(x, r);
      var new_tree := update_height(new_left, k, r);

      var hl := height(new_tree.left);
      var hr := height(new_tree.right);

      match new_tree
      case Leaf => Leaf
      case Node(l1, _, key, r1) =>
        if abs(hl - hr) <= 1 then
          new_tree
        else
          equil(l1, key, r1)
}
