module BinarySearchTree

abstract type btree = 
  | Leaf : btree
  | Node : btree -> nat -> btree -> btree

let rec exists_in (n:nat) (t:btree) : GTot bool =
  match t with 
  | Leaf -> false
  | Node t1 m t2 -> 
      if n = m then true else 
      if n < m then n `exists_in` t1 
               else n `exists_in` t2

let empty () : GTot btree = Leaf

let rec insert (t:btree) (n:nat) : GTot btree =
  match t with 
  | Leaf -> Node Leaf n Leaf
  | Node t1 m t2 -> 
      if n = m then Node t1 m t2 else
      if n < m then Node (insert t1 n) m t2
               else Node t1 m (insert t2 n)

let rec is_sorted_left (t:btree) (n:nat) : GTot bool = 
  match t with
  | Leaf -> true
  | Node t1 m t2 -> t1 `is_sorted_left` m && 
                    m < n && 
                    t2 `is_sorted_right` m

and is_sorted_right (t:btree) (n:nat) : GTot bool = 
  match t with
  | Leaf -> true
  | Node t1 m t2 -> t1 `is_sorted_left` m && 
                    m > n && 
                    t2 `is_sorted_right` m

let rec is_sorted (t:btree) : GTot bool =
  match t with
  | Leaf -> true
  | Node t1 n t2 -> t1 `is_sorted_left` n && t2 `is_sorted_right` n

abstract type stree = 
  t:btree{is_sorted t}

let lemma_empty_is_sorted () : Lemma (is_sorted (empty ())) = 
  ()

let rec lemma_insert_is_sorted (t:stree) (n:nat) : Lemma (is_sorted (insert t n)) = 
  match t with
  | Leaf -> ()
  | Node t1 m t2 -> 
      if n = m then () else
      if n < m then lemma_insert_is_sorted t1 n
               else lemma_insert_is_sorted t2 n

let rec lemma_exists_insert_equal (t:stree) (n:nat) : Lemma (requires (n `exists_in` t))
                                                            (ensures  (insert t n = t)) = 
  match t with
  | Node t1 m t2 -> 
      if n = m then () else 
      if n < m then lemma_exists_insert_equal t1 n
               else lemma_exists_insert_equal t2 n

let rec lemma_insert_exists (t:stree) (n:nat) : Lemma (n `exists_in` (insert t n)) =
  match t with
  | Leaf -> ()
  | Node t1 m t2 -> 
      if n = m then () else
      if n < m then lemma_insert_exists t1 n
               else lemma_insert_exists t2 n

(*
let rec lemma_sorted_left_is_sorted (t:btree) (n:nat) : Lemma (requires (is_sorted_left t n))
                                                              (ensures  (is_sorted t)) 
                                                              [SMTPat (is_sorted_left t n)] =
  match t with
  | Leaf -> ()
  | Node t1 m t2 -> lemma_sorted_left_is_sorted t1 m;                    
                    lemma_sorted_right_is_sorted t2 m

and lemma_sorted_right_is_sorted (t:btree) (n:nat) : Lemma (requires (is_sorted_right t n))
                                                           (ensures  (is_sorted t)) 
                                                           [SMTPat (is_sorted_right t n)] =
  match t with
  | Leaf -> ()
  | Node t1 m t2 -> lemma_sorted_left_is_sorted t1 m;
                    lemma_sorted_right_is_sorted t2 m
*)
