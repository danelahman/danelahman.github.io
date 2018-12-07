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
  | Node : btree -> nat -> btree -> btree

(* 

  Task 1.1: Implement a tree search / containment predicate for binary trees. 

            Hint: While at this point we have not made precise that `t:btree` is a **search** tree, implement 
            `btree_contains` as if it was, i.e., assuming that elements in the left subtree of a node are 
            strictly smaller than the value stored at that node, and vice versa for right subtrees.    

  Note: The various operations on purely functional search trees below are defined using the GTot effect 
        (i.e., ghost code) to ensure that we will later use them only in a purely specificational role.

*)

private let rec btree_contains (t:btree) (n:nat) : GTot bool =
  match t with 
  | Leaf -> false
  | Node t1 m t2 -> 
      if n = m then true else 
      if n < m then t1 `btree_contains` n
               else t2 `btree_contains` n

(* 

  Task 1.2: Define empty binary trees and insertion into binary (search) trees.

*)

private let empty_btree () : GTot btree = Leaf

private let rec btree_insert (t:btree) (n:nat) : GTot btree =
  match t with 
  | Leaf -> Node Leaf n Leaf
  | Node t1 m t2 -> 
      if n = m then Node t1 m t2 else
      if n < m then Node (btree_insert t1 n) m t2
               else Node t1 m (btree_insert t2 n)

(*

  Task 1.3: Define a sortedness predicate over `btree` that holds when a given tree is sorted in the 
            sense that for a node storing a value `v`, all values in its left subtree are strictly 
            smaller than `v`, and all values in its right subtree are strictly greater than `v`.

*)

private let rec sorted_left_of (t:btree) (n:nat) : GTot bool = 
  match t with
  | Leaf -> true
  | Node t1 m t2 -> t1 `sorted_left_of` m && 
                    m < n && 
                    t2 `sorted_right_of` m

and sorted_right_of (t:btree) (n:nat) : GTot bool = 
  match t with
  | Leaf -> true
  | Node t1 m t2 -> t1 `sorted_left_of` m && 
                    m > n && 
                    t2 `sorted_right_of` m

private let rec sorted (t:btree) : GTot bool =
  match t with
  | Leaf -> true
  | Node t1 n t2 -> t1 `sorted_left_of` n && 
                    t2 `sorted_right_of` n


(** PART 2 **)

(* Binary search trees are defined as a refinement of the `btree` type from above. *)

abstract type stree = t:btree{sorted t}

(* Useful lemmas about sortedness and the tree operations defined above *)

private let rec lemma_btree_insert_is_sorted (t:btree) (n:nat) 
  : Lemma (requires (sorted t))
          (ensures  (sorted (btree_insert t n))) = 
  match t with
  | Leaf -> ()
  | Node t1 m t2 -> 
      if n = m then () else
      if n < m then lemma_btree_insert_is_sorted t1 n
               else lemma_btree_insert_is_sorted t2 n

private let rec lemma_btree_insert_contains (t:btree) (n:nat) 
  : Lemma (requires (sorted t))
          (ensures  ((btree_insert t n) `btree_contains` n)) =
  match t with
  | Leaf -> ()
  | Node t1 m t2 -> 
      if n = m then () else
      if n < m then lemma_btree_insert_contains t1 n
               else lemma_btree_insert_contains t2 n

private let rec lemma_contains_btree_insert_equal (t:btree) (n:nat) 
  : Lemma (requires (sorted t && t `btree_contains` n))
          (ensures  (btree_insert t n = t)) = 
  match t with
  | Node t1 m t2 -> 
      if n = m then () else 
      if n < m then lemma_contains_btree_insert_equal t1 n
               else lemma_contains_btree_insert_equal t2 n

private let rec lemma_distinct_btree_insert_contains (t:btree) (n m:nat)
  : Lemma (requires ((btree_insert t n) `btree_contains` m))
          (ensures  (t `btree_contains` m \/ n = m)) = 
  match t with 
  | Leaf -> ()
  | Node t1 k t2 -> 
      if n = k then () else 
      if n < k then (Classical.or_elim #((btree_insert t1 n) `btree_contains` m) 
                                       #(not((btree_insert t1 n) `btree_contains` m)) 
                                       #(fun _ -> (Node t1 k t2) `btree_contains` m \/ n = m) 
                                       (fun _ -> lemma_distinct_btree_insert_contains t1 n m) 
                                       (fun _ -> ()))
               else (Classical.or_elim #((btree_insert t2 n) `btree_contains` m) 
                                       #(not((btree_insert t2 n) `btree_contains` m)) 
                                       #(fun _ -> (Node t1 k t2) `btree_contains` m \/ n = m) 
                                       (fun _ -> lemma_distinct_btree_insert_contains t2 n m) 
                                       (fun _ -> ()))

private let lemma_distinct_btree_insert_not_contains (t:btree) (n m:nat)
  : Lemma (requires (not (t `btree_contains` m) /\ n <> m))
          (ensures  (not ((btree_insert t n) `btree_contains` m))) = 
  Classical.move_requires (fun _ -> lemma_distinct_btree_insert_contains t n m) ()

(*

  Task 2.1: Define search/containment, creation of empty trees, and insertion operations for binary search trees.

*)

let stree_contains (t:stree) (n:nat) : GTot bool =
  btree_contains t n

let empty_stree () : GTot stree = 
  empty_btree ()

let stree_insert (t:stree) (n:nat) : GTot stree = 
  lemma_btree_insert_is_sorted t n; 
  btree_insert t n

(*

  Task 2.1: Prove correct three expected properties of binary search trees. 

*)

let rec lemma_insert_contains (t:stree) (n:nat) 
  : Lemma ((stree_insert t n) `stree_contains` n) =
  lemma_btree_insert_contains t n

let rec lemma_contains_insert_equal (t:stree) (n:nat) 
  : Lemma (requires (t `stree_contains` n))
          (ensures  (stree_insert t n = t)) = 
  lemma_contains_btree_insert_equal t n

let lemma_distinct_insert_not_contains (t:stree) (n m:nat)
  : Lemma (requires (not (t `stree_contains` m) /\ n <> m))
          (ensures  (not ((stree_insert t n) `stree_contains` m))) = 
  lemma_distinct_btree_insert_not_contains t n m


(** PART 3 **)

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
            reasoning about specifications in `FStar.Classical.fsti` and `FStar.StrongExcludedMiddle.fst`

*)

let rec wf (r:mtree) (t:stree) (h:heap) : GTot (option (Set.set nat)) (decreases t) =
  match t , StrongExcludedMiddle.strong_excluded_middle (h `contains` r) , sel h r with
  | Leaf , true , None -> Some (only r)
  | Node t1 n t2 , true , Some nd -> (
      match (wf nd.left t1 h) , (n = nd.value) , (wf nd.right t2 h) with
      | Some s1 , true , Some s2 -> (
          match not (Set.mem (addr_of r) s1) , not (Set.mem (addr_of r) s2) , 
                StrongExcludedMiddle.strong_excluded_middle (Set.disjoint s1 s2) with 
          | true , true , true -> Some (Set.union (only r) (Set.union s1 s2))
          | _ -> None
        )
      | _ -> None
    )
  | _ -> None

let is_stree (r:mtree) (t:stree) (h:heap) : GTot bool = Some? (wf r t h)

(*

  Task 3.2: Define a stateful search function whose behaviour is specified by the search function / containment
            predicate for the purely functional search trees that we defined in Part 2 of this exercise.

            Hint: You will need to strengthen the specification of `search` to verify `BinarySearchTreeClient`.

  Note: Here we follow a common pattern in verification of threading a ghost state through our programs, where 
        the ghost state (here, `t:erased stree`) is the purely functional specification of our mutable stateful 
        code. We have wrapped `stree` in `erased` to ensure that it cannot be used computationally relevantly 
        in user code (in that sense, `erased` is similar to the `GTot` effect). You can find more about the 
        `erased` type in the F* standard library in `FStar.Ghost`, including operations that you will need to use.

*)

let rec search (t:erased stree) (r:mtree) (n:nat) 
  : ST bool (requires (fun h0 -> is_stree r (reveal t) h0))
            (ensures  (fun h0 b h1 -> h0 == h1 /\ 
                                      b = (reveal t) `stree_contains` n)) =
  match !r with 
  | None -> false
  | Some nd -> 
      if n = nd.value then true else 
      if n < nd.value then (let t1 = hide (match (reveal t) with 
                                           | Node t1 _ _ -> t1) in 
                            search t1 nd.left n)
                      else (let t2 = hide (match (reveal t) with 
                                           | Node _ _ t2 -> t2) in
                            search t2 nd.right n)

(*

  Task 3.3: Define a stateful function that creates an empty binary search tree. 

            Hint: You will need to strengthen the specification of `empty` to verify `BinarySearchTreeClient`. 

*)

let create () 
  : ST (erased stree * mtree) (requires (fun _ -> True))
                              (ensures  (fun h0 (t,r) h1 -> 
                                 reveal t = empty_stree () /\
                                 fresh r h0 h1 /\
                                 modifies !{} h0 h1 /\
                                 wf r (reveal t) h1 == Some (only r))) =
  hide Leaf , alloc None

(*

  Task 3.3: Define a stateful insertion function for mutable binary search trees. 

            Hint: You will need to strengthen the specification of `insert` to verify `BinarySearchTreeClient`. 

*)

let rec lemma_disjoint_wf_unchanged (r:mtree) (t:stree) (s:Set.set nat) (h0 h1:heap)
  : Lemma (requires (Some? (wf r t h0) /\ 
                     Set.disjoint (Some?.v (wf r t h0)) s /\ 
                     modifies s h0 h1))
          (ensures  (wf r t h0 == wf r t h1)) (decreases t)
          [SMTPat (wf r t h0); SMTPat (modifies s h0 h1)]= 
  match t with
  | Leaf -> ()
  | Node t1 n t2 -> 
      let (Some nd) = sel h0 r in 
      lemma_disjoint_wf_unchanged nd.left t1 s h0 h1;
      lemma_disjoint_wf_unchanged nd.right t2 s h0 h1

let rec lemma_wf_addrs_in (r:mtree) (t:stree) (h:heap)
  : Lemma (requires (Some? (wf r t h)))
          (ensures  (forall r' . Set.mem r' (Some?.v (wf r t h)) ==> ~(addr_unused_in r' h))) 
          (decreases t)
          [SMTPat (wf r t h)] = 
  match t with 
  | Leaf -> ()
  | Node t1 n t2 -> 
      let (Some nd) = sel h r in
      lemma_wf_addrs_in nd.left t1 h;
      lemma_wf_addrs_in nd.right t2 h

(* Insertion into a mutable binary search tree *)

let fresh_extension (s0 s1:Set.set nat) (h:heap) = 
  Set.subset s0 s1 /\
  (forall r . (not (Set.mem r s0) /\ Set.mem r s1) ==> addr_unused_in r h)

let rec insert (t:erased stree) (r:mtree) (n:nat) 
  : ST (erased stree) (requires (fun h0 -> is_stree r (reveal t) h0))
                      (ensures  (fun h0 t' h1 -> 
                         reveal t' = stree_insert (reveal t) n /\
                         is_stree r (reveal t') h1 /\ (
                         let (Some s0) = wf r (reveal t) h0 in 
                         let (Some s1) = wf r (reveal t') h1 in
                         modifies s0 h0 h1 /\
                         fresh_extension s0 s1 h0))) = 
  recall r;
  match !r with
  | None -> (
      let t1,r1 = create () in
      let t2,r2 = create () in  
      r := Some ({left = r1; value = n; right = r2});
      hide (Node (reveal t1) n (reveal t2)))
  | Some nd -> 
      if n = nd.value then t else
      if n < nd.value then (let t1 = hide (match (reveal t) with 
                                           | Node t1 _ _ -> t1) in
                            let t2 = hide (match (reveal t) with 
                                           | Node _ _ t2 -> t2) in
                            let t1' = insert t1 (nd.left) n in 
                            hide (Node (reveal t1') nd.value (reveal t2)))
                      else (let t1 = hide (match (reveal t) with 
                                           | Node t1 _ _ -> t1) in
                            let t2 = hide (match (reveal t) with 
                                           | Node _ _ t2 -> t2) in
                            let t2' = insert t2 (nd.right) n in 
                            hide (Node (reveal t1) nd.value (reveal t2')))

(** PART 4 **)

(*

  Task 4.1: Verify `BinarySearchTreeClient` to check that the specifications and definitions 
            that you defined above indeed work as expected in a composite stateful program.

*)
