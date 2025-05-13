function max(a : int, b : int) : int {
  if (a < b) then b else a
}

function abs(a : int) : int {
  if (a < 0) then -a else a
}

datatype AVL = Leaf | Node(left:AVL, height: nat, key:int, right:AVL)

function height(t : AVL) : nat {
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
  case Node(l, h, x, r) => h == height(t) && isAVL(l) && isAVL(r)
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

function update_height(l: AVL, x: int, r: AVL): AVL
{
  Node(l, 1 + max(height(l), height(r)), x, r)
}

lemma insert_aux_preserves_ordering(x: int, t: AVL)
  requires isAVL(t)
  ensures
    match t
    case Leaf => true
    case Node(l, h, k, r) =>
      (x < k ==>
         (forall z :: z in treetoset(insert_aux(x, l)) ==> z < k) &&
         (forall z :: z in treetoset(r) ==> z > k)) &&
      (x > k ==>
         (forall z :: z in treetoset(l) ==> z < k) &&
         (forall z :: z in treetoset(insert_aux(x, r)) ==> z > k))
  decreases t
{
  match t {
    case Leaf => {}
    case Node(l, h, k, r) =>
      if x < k {
        insert_aux_preserves_ordering(x, l);
      } else if x > k {
        insert_aux_preserves_ordering(x, r);
      }
  }
}

function insert_aux(x: int, t: AVL): (res: AVL)
  decreases t
  ensures t == Leaf ==> res == Node(Leaf, 1, x, Leaf)
  ensures t != Leaf ==> treetoset(res) == treetoset(t) + {x}
  ensures t != Leaf ==>
            match t
            case Node(l, h, k, r) =>
              (x < k ==> res == Node(insert_aux(x, l), h, k, r)) &&
              (x >= k ==> res == Node(l, h, k, insert_aux(x, r)))
{
  match t
  case Leaf => Node(Leaf, 1, x, Leaf)
  case Node(l, h, k, r) =>
    if x < k then Node(insert_aux(x, l), h, k, r)
    else if x > k then Node(l, h, k, insert_aux(x, r))
    else
      insert_aux_preserves_ordering(x, t);
      t
}

function insert(x: int, t: AVL): (res: AVL)
  decreases t
  requires isAVL(t)
  ensures isAVL(res)
  ensures treetoset(res) == treetoset(t) + {x}
{
  match t
  case Leaf => Node(Leaf, 1, x, Leaf)
  case Node(l, h, k, r) =>
    var new_tree := if x < k
                    then update_height(insert(x, l), k, r)
                    else if x > k
                      then update_height(l, k, insert(x, r))
                      else t;

    // check if rebalancing is needed
    var hl := height(new_tree.left);
    var hr := height(new_tree.right);

    if abs(hl - hr) <= 1 then new_tree
    else equil(new_tree.left, new_tree.key, new_tree.right)
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

        if abs(hl - hr) <= 1 then
          new_tree
        else
          equil(new_tree.left, new_tree.key, new_tree.right)

    // delete on the left
    else if x < k then
      var new_left := delete(x, l);
      var new_tree := update_height(new_left, k, r);

      var hl := height(new_tree.left);
      var hr := height(new_tree.right);

      if abs(hl - hr) <= 1 then
        new_tree
      else
        equil(new_tree.left, new_tree.key, new_tree.right)

    // delete on the right
    else
      var new_left := delete(x, r);
      var new_tree := update_height(new_left, k, r);

      var hl := height(new_tree.left);
      var hr := height(new_tree.right);

      if abs(hl - hr) <= 1 then
        new_tree
      else
        equil(new_tree.left, new_tree.key, new_tree.right)
}

// TODO: e)
