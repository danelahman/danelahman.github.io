module BinarySearchTree

(* Binary trees *)

private abstract type btree = 
  | Leaf : btree
  | Node : btree -> nat -> btree -> btree

(* Search function / containment predicate for binary (search) trees *)

private let rec btree_contains (t:btree) (n:nat) : GTot bool =
  match t with 
  | Leaf -> false
  | Node t1 m t2 -> 
      if n = m then true else 
      if n < m then t1 `btree_contains` n
               else t2 `btree_contains` n

(* Empty binary tree *)

private let empty_btree () : GTot btree = Leaf

(* Insertion into a binary (search) tree *)

private let rec btree_insert (t:btree) (n:nat) : GTot btree =
  match t with 
  | Leaf -> Node Leaf n Leaf
  | Node t1 m t2 -> 
      if n = m then Node t1 m t2 else
      if n < m then Node (btree_insert t1 n) m t2
               else Node t1 m (btree_insert t2 n)

(* Sortedness predicate for binary (search) trees *)

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

(* Useful lemmas about sortedness and the tree operations defined above *)

private let rec lemma_btree_insert_is_sorted (t:btree) (n:nat) : Lemma (requires (sorted t))
                                                                       (ensures  (sorted (btree_insert t n))) = 
  match t with
  | Leaf -> ()
  | Node t1 m t2 -> 
      if n = m then () else
      if n < m then lemma_btree_insert_is_sorted t1 n
               else lemma_btree_insert_is_sorted t2 n

private let rec lemma_btree_insert_exists (t:btree) (n:nat) : Lemma (requires (sorted t))
                                                                    (ensures  ((btree_insert t n) `btree_contains` n)) =
  match t with
  | Leaf -> ()
  | Node t1 m t2 -> 
      if n = m then () else
      if n < m then lemma_btree_insert_exists t1 n
               else lemma_btree_insert_exists t2 n

private let rec lemma_exists_btree_insert_equal (t:btree) (n:nat) : Lemma (requires (sorted t && t `btree_contains` n))
                                                                          (ensures  (btree_insert t n = t)) = 
  match t with
  | Node t1 m t2 -> 
      if n = m then () else 
      if n < m then lemma_exists_btree_insert_equal t1 n
               else lemma_exists_btree_insert_equal t2 n

(* Binary search trees = binary trees as defined above that are sorted *)

abstract type stree = 
  t:btree{sorted t}

(* Binary search tree operations, derived from tree operations defined above*)

let contains (t:stree) (n:nat) : GTot bool =
  btree_contains t n

let empty () : GTot stree = 
  empty_btree ()

let insert (t:stree) (n:nat) : GTot stree = 
  lemma_btree_insert_is_sorted t n; 
  btree_insert t n

(* Sanity check lemmas *)

private let lemma_contains_equals (t:stree) (n:nat) : Lemma (t `btree_contains` n = t `contains` n) = 
  ()

private let lemma empty_equals () : Lemma (empty_btree () = empty ()) = 
  ()

private let lemma_insert_equals (t:stree) (n:nat) : Lemma (btree_insert t n = insert t n) = 
  ()
  
(* Important properties of binary search trees *)

let rec lemma_insert_is_sorted (t:stree) (n:nat) : Lemma (sorted (btree_insert t n)) = 
  lemma_btree_insert_is_sorted t n

let rec lemma_insert_exists (t:stree) (n:nat) : Lemma ((btree_insert t n) `btree_contains` n) =
  lemma_btree_insert_exists t n

let rec lemma_exists_insert_equal (t:stree) (n:nat) : Lemma (requires (t `btree_contains` n))
                                                            (ensures  (btree_insert t n = t)) = 
  lemma_exists_btree_insert_equal t n
