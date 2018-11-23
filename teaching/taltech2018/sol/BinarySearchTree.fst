module BinarySearchTree

abstract type btree = 
  | Leaf : btree
  | Node : btree -> nat -> btree -> btree

let rec is_sorted_left (t:btree) (n:nat) : GTot bool = 
  match t with
  | Leaf -> true
  | Node t1 m t2 -> t1 `is_sorted_left` m && m < n && t2 `is_sorted_right` m

and is_sorted_right (t:btree) (n:nat) : GTot bool = 
  match t with
  | Leaf -> true
  | Node t1 m t2 -> t1 `is_sorted_left` m && m > n && t2 `is_sorted_right` m

let rec is_sorted (t:btree) : GTot bool =
  match t with
  | Leaf -> true
  | Node t1 n t2 -> t1 `is_sorted_left` n && t2 `is_sorted_right` n

abstract type stree = 
  t:btree{is_sorted t}

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

let rec search (t:stree) (n:nat) : GTot bool =
  match t with 
  | Leaf -> false
  | Node t1 m t2 -> 
      if n = m then true else 
      if n < m then search t1 n else
                    search t2 n
