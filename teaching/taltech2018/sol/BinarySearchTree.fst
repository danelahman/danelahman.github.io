module BinarySearchTree

(* Binary node-labelled trees *)

private type btree = 
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

private let rec lemma_btree_insert_is_sorted (t:btree) (n:nat) 
  : Lemma (requires (sorted t))
          (ensures  (sorted (btree_insert t n))) = 
  match t with
  | Leaf -> ()
  | Node t1 m t2 -> 
      if n = m then () else
      if n < m then lemma_btree_insert_is_sorted t1 n
               else lemma_btree_insert_is_sorted t2 n

private let rec lemma_btree_insert_exists (t:btree) (n:nat) 
  : Lemma (requires (sorted t))
          (ensures  ((btree_insert t n) `btree_contains` n)) =
  match t with
  | Leaf -> ()
  | Node t1 m t2 -> 
      if n = m then () else
      if n < m then lemma_btree_insert_exists t1 n
               else lemma_btree_insert_exists t2 n

private let rec lemma_exists_btree_insert_equal (t:btree) (n:nat) 
  : Lemma (requires (sorted t && t `btree_contains` n))
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

private let lemma_contains_equals (t:stree) (n:nat) 
  : Lemma (t `btree_contains` n = t `contains` n) = 
  ()

private let lemma empty_equals () 
  : Lemma (empty_btree () = empty ()) = 
  ()

private let lemma_insert_equals (t:stree) (n:nat) 
  : Lemma (btree_insert t n = insert t n) = 
  ()
  
(* Important properties of binary search trees *)

let rec lemma_insert_is_sorted (t:stree) (n:nat) 
  : Lemma (sorted (btree_insert t n)) = 
  lemma_btree_insert_is_sorted t n

let rec lemma_insert_exists (t:stree) (n:nat) 
  : Lemma ((btree_insert t n) `btree_contains` n) =
  lemma_btree_insert_exists t n

let rec lemma_exists_insert_equal (t:stree) (n:nat) 
  : Lemma (requires (t `btree_contains` n))
          (ensures  (btree_insert t n = t)) = 
  lemma_exists_btree_insert_equal t n


(* ------------------------------------------------------ *)
(* ------------------------------------------------------ *)

//module H = FStar.Heap

open FStar.Ghost
open FStar.ST

abstract noeq type node = {
  left  : treeptr;
  value : nat;
  right : treeptr
} 
and treeptr = ref (option node)

let heap = FStar.Heap.heap
let sel h (r:treeptr) = FStar.Heap.sel h r
let upd h (r:treeptr) v = FStar.Heap.upd h r v 

let is_leaf (r:treeptr) (h:heap) = None? (sel h r)
let is_node (r:treeptr) (h:heap) = Some? (sel h r)

let rec is_stree (r:treeptr) (t:stree) (h:heap) : GTot bool (decreases t) =
  match t with 
  | Leaf -> is_leaf r h
  | Node t1 n t2 -> 
      is_node r h &&
      (match (sel h r) with
       | Some nd -> is_stree nd.left t1 h &&
                    n = nd.value &&
                    is_stree nd.right t2 h)

let rec search (#t:erased stree) (r:treeptr) (n:nat) 
  : ST bool (requires (fun h0 -> is_stree r (reveal t) h0))
            (ensures  (fun h0 b h1 -> h0 == h1 /\ (reveal t) `contains` n <==> b = true)) =
  match !r with 
  | None -> false
  | Some nd -> 
      if n = nd.value then true else 
      if n < nd.value then (let t1 = hide (match (reveal t) with | Node t1 _ _ -> t1) in 
                            search #t1 nd.left n)
                      else (let t2 = hide (match (reveal t) with | Node _ _ t2 -> t2) in
                            search #t2 nd.right n)

let create () : ST treeptr (requires (fun _ -> True))
                           (ensures  (fun _ r h1 -> is_leaf r h1)) =
  alloc None

let rec insert (#t:erased stree) (r:treeptr) (n:nat) 
  : ST unit (requires (fun h0 -> is_stree r (reveal t) h0))
            (ensures  (fun h0 _ h1 -> True))

