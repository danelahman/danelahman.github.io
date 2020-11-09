module BinarySearchTree

(*

  Exercise 7.

  In this exercise you will practice writing and verifying both purely functional and stateful programs. 
  
  The goal is to implement mutable binary search trees whose specifications are given by their purely 
  functional implementation. For simplicity, we only consider creation of empty binary search trees, 
  insertion into existing binary search trees, and searching from binary search trees. Implementing 
  other operations, such as deletion, is left as a bonus exercise for the more motivated students.

  If you haven't seen such trees before, see e.g. https://en.wikipedia.org/wiki/Binary_search_tree.

  This exercise is divided into four parts:

   - Part 1: Purely functional implementation of operations on binary trees.

   - Part 2: Purely functional implementation of binary search trees (as a refinement of Part 1).

   - Part 3: Stateful implementation of (mutable) binary search trees (with specifications by Part 2).

   - Part 4: Verify the client code in `BinarySearchTreeClient.fst` that tests whether the code and 
             specifications you wrote in this exercise work as expected in a composite program. 

*)

(** PART 1 **)

(* Inductive definition of binary trees. For simplicity, containing only natural numbers. *)

private type btree = 
  | Leaf : btree
  | Node : (left:btree) -> (value:nat) -> (right:btree) -> btree

(* 

  Task 1.1: Implement a tree search / containment predicate for binary trees. 

            Hint: While at this point we have not made precise that `t:btree` is a **search** tree, implement 
            `btree_contains` as if it was, i.e., assuming that elements in the left subtree of a node are 
            strictly smaller than the value stored at that node, and vice versa for right subtrees.    

  Note: The various operations on purely functional search trees below are defined using the GTot effect 
        (i.e., ghost code) to ensure that we will later use them only in a purely specificational role.

*)

private let rec btree_contains (t:btree) (n:nat) : GTot bool =
  admit ()

(* 

  Task 1.2: Define the empty binary tree and insertion into binary trees. For the latter, again assume as 
            if you were working with binary **search** trees, i.e., insert the given value `n` so that if 
            the given tree `t` happens to be a binary search tree, so will be the returned binary tree.

*)

private let empty_btree () : GTot btree = 
  admit ()

private let rec btree_insert (t:btree) (n:nat) : GTot btree =
  admit ()

(*

  Task 1.3: Define a sortedness predicate over `btree` that holds when a given tree is sorted in the 
            sense that for a node storing a value `v`, all values in its left subtree are strictly 
            smaller than `v`, and all values in its right subtree are strictly greater than `v`.

*)

private let rec sorted (t:btree) : GTot bool =
  admit ()


(** PART 2 **)

(* Binary search trees are defined as a refinement of the `btree` type from above. *)

type stree = t:btree{sorted t}

(*

  Task 2.1: Define search/containment, creation of empty trees, and insertion operations for binary search trees.

*)

let stree_contains (t:stree) (n:nat) : GTot bool =
  admit ()

let empty_stree () : GTot stree = 
  admit ()

let stree_insert (t:stree) (n:nat) : GTot stree = 
  admit ()

(*

  Task 2.2: Prove correct three expected properties of binary search trees. 

*)

let rec lemma_insert_contains (t:stree) (n:nat) 
  : Lemma ((stree_insert t n) `stree_contains` n) =
  admit ()

let rec lemma_contains_insert_equal (t:stree) (n:nat) 
  : Lemma (requires (t `stree_contains` n))
          (ensures  (stree_insert t n = t)) = 
  admit ()

let lemma_distinct_insert_not_contains (t:stree) (n m:nat)
  : Lemma (requires (not (t `stree_contains` m) /\ n <> m))
          (ensures  (not ((stree_insert t n) `stree_contains` m))) = 
  admit ()


(** PART 3 **)

(*

  Importing standard library modules to do with erased ghost code (see the note below) and 
  stateful programming (heaps, the `ST` effect, etc). Hint: You will highly likely need to 
  have a look at these libraries and use the functionality they provide in your solution.

*)

open FStar.Ghost
open FStar.Heap
open FStar.ST

(*

  Mutable binary trees (`mtree`) are defined as a memory reference to a record that stores the 
  left subtree, the value stored at a given node of the tree, and the right subtree. As usual, 
  the definition is given using two mutually recursively defined types (`treeptr` and `node`).  

*)

noeq type node = {
  left  : treeptr;
  value : nat;
  right : treeptr
} 
and treeptr = ref (option node)

let mtree = treeptr

(*

  Task 3.1: Define a predicate that holds when a given mutable binary search tree (`r:mtree`) agrees 
            with a given purely functional binary search tree (`t:stree`) in some heap `h:heap`. That 
            is, `is_stree` should return true when the shapes and contents of `r` in `h` matches `t`.

            Hint: You might find it useful to have a look at and use the libraries for (classical) logical 
            reasoning about specifications given in `FStar.Classical` and `FStar.StrongExcludedMiddle`.

*)

let is_stree (r:mtree) (t:stree) (h:heap) : GTot bool = 
  admit ()

(*

  Task 3.2: Define a stateful search function whose behaviour is specified by the search function / containment
            predicate for the purely functional search trees that we defined in Part 2 of this exercise.

            Hint: You will need to strengthen the specification of `search` to verify `BinarySearchTreeClient`.

  Note: Here we follow a common pattern in verification of threading a ghost state through our programs, where 
        the ghost state (`t:erased stree`) is the purely functional specification of our mutable stateful code.
        We have wrapped `stree` in the `erased` type to ensure that it cannot be used computationally relevantly 
        in user code (in that sense, `erased` is similar to the `GTot` effect). As a result, all the uses of the
        purely functional search trees in this stateful code will be erased to unit-values during code extraction. 
        You can find more about the `erased` type and how to use it in the standard library in `FStar.Ghost`.

*)

let rec search (t:erased stree) (r:mtree) (n:nat) 
  : ST bool (requires (fun h0 -> is_stree r (reveal t) h0))
            (ensures  (fun h0 b h1 -> b = (reveal t) `stree_contains` n)) =
  admit ()

(*

  Task 3.3: Define a stateful function that creates an empty binary search tree. 

            Hint: You will need to strengthen the specification of `empty` to verify `BinarySearchTreeClient`. 

*)

let create () 
  : ST (erased stree * mtree) (requires (fun _ -> True))
                              (ensures  (fun h0 (t,r) h1 -> 
                                 reveal t = empty_stree ())) =
  admit ()

(*

  Task 3.3: Define a stateful insertion function for mutable binary search trees. 

            Hint: You will need to strengthen the specification of `insert` to verify `BinarySearchTreeClient`. 

*)

(* Insertion into a mutable binary search tree *)

let rec insert (t:erased stree) (r:mtree) (n:nat) 
  : ST (erased stree) (requires (fun h0 -> is_stree r (reveal t) h0))
                      (ensures  (fun h0 t' h1 -> 
                         reveal t' = stree_insert (reveal t) n)) = 
  admit ()
  
(** PART 4 **)

(*

  Task 4.1: Verify `BinarySearchTreeClient` to check that the specifications and definitions 
            that you defined above indeed work as expected in a composite stateful program.

*)
