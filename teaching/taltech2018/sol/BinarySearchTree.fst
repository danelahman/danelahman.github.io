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

(* Binary search trees = binary trees as defined above that are sorted *)

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

(* Binary search tree operations *)

let stree_contains (t:stree) (n:nat) : GTot bool =
  btree_contains t n

let empty_stree () : GTot stree = 
  empty_btree ()

let stree_insert (t:stree) (n:nat) : GTot stree = 
  lemma_btree_insert_is_sorted t n; 
  btree_insert t n

(* Sanity check lemmas *)

private let lemma_contains_equals (t:stree) (n:nat) 
  : Lemma (t `btree_contains` n = t `stree_contains` n) = 
  ()

private let lemma empty_equals () 
  : Lemma (empty_btree () = empty_stree ()) = 
  ()

private let lemma_insert_equals (t:stree) (n:nat) 
  : Lemma (btree_insert t n = stree_insert t n) = 
  ()
  
(* Important properties of binary search trees *)

let rec lemma_insert_exists (t:stree) (n:nat) 
  : Lemma ((stree_insert t n) `stree_contains` n) =
  lemma_btree_insert_exists t n

let rec lemma_exists_insert_equal (t:stree) (n:nat) 
  : Lemma (requires (t `stree_contains` n))
          (ensures  (stree_insert t n = t)) = 
  lemma_exists_btree_insert_equal t n


(* ------------------------------------------------------ *)
(* ------------------------------------------------------ *)


open FStar.Ghost
open FStar.Heap
open FStar.ST

noeq type node = {
  left  : treeptr;
  value : nat;
  right : treeptr
} 
and treeptr = ref (option node)

let mtree = treeptr

let rec wf (r:mtree) (t:stree) (h:heap) : GTot (option (Set.set nat)) (decreases t) =
  match t , StrongExcludedMiddle.strong_excluded_middle (contains h r) , sel h r with
  | Leaf , true , None -> Some (only r)
  | Node t1 n t2 , true , Some nd -> (
      match (wf nd.left t1 h) , (n = nd.value) , (wf nd.right t2 h) with
      | Some s1 , true , Some s2 -> (
          match not (Set.mem (addr_of r) s1) , not (Set.mem (addr_of r) s2) , StrongExcludedMiddle.strong_excluded_middle (Set.disjoint s1 s2) with 
          | true , true , true -> Some (Set.union (only r) (Set.union s1 s2))
          | _ -> None
        )
      | _ -> None
    )
  | _ -> None

let is_stree (r:mtree) (t:stree) (h:heap) : GTot bool = Some? (wf r t h)


(*let rec is_stree (r:mtree) (t:stree) (h:heap) : GTot bool (decreases t) =
  match t with 
  | Leaf -> None? (sel h r)
  | Node t1 n t2 -> 
      Some? (sel h r) &&
      (match (sel h r) with
       | Some nd -> is_stree nd.left t1 h &&
                    n = nd.value &&
                    is_stree nd.right t2 h)*)

let rec search (t:erased stree) (r:mtree) (n:nat) 
  : ST bool (requires (fun h0 -> is_stree r (reveal t) h0))
            (ensures  (fun h0 b h1 -> h0 == h1 /\ b = (reveal t) `stree_contains` n)) =
  match !r with 
  | None -> false
  | Some nd -> 
      if n = nd.value then true else 
      if n < nd.value then (let t1 = hide (match (reveal t) with | Node t1 _ _ -> t1) in 
                            search t1 nd.left n)
                      else (let t2 = hide (match (reveal t) with | Node _ _ t2 -> t2) in
                            search t2 nd.right n)

let create () 
  : ST (erased stree * mtree) (requires (fun _ -> True))
                              (ensures  (fun h0 (t,r) h1 -> fresh r h0 h1 /\
                                                            modifies !{} h0 h1 /\
                                                            reveal t = empty_stree () /\
                                                            wf r (reveal t) h1 == Some (only r))) =
  hide Leaf , alloc None

(*
let rec addrs_of_tree (r:mtree) (t:stree) (h:heap{is_stree r t h}) 
  : GTot (Set.set nat) (decreases t) = 
  match t with
  | Leaf -> Set.empty
  | Node t1 n t2 -> 
      match (sel h r) with
      | Some nd -> Set.union (Set.singleton (addr_of r)) 
                             (Set.union (addrs_of_tree nd.left t1 h) 
                                        (addrs_of_tree nd.right t2 h))
*)

(*
let lemma_is_stree_node (t1 t2:erased stree) (r:mtree) (nd:node) (s1 s2:Set.set nat) (h:heap)
  : Lemma (requires (contains h r /\
                     sel h r == Some nd /\
                     wf (nd.left) (reveal t1) h == Some s1 /\ 
                     wf (nd.right) (reveal t2) h == Some s2 /\ 
                     not (Set.mem (addr_of r) s1) /\
                     Set.disjoint s1 s2 /\
                     not (Set.mem (addr_of r) s2) /\
                     sorted (Node (reveal t1) nd.value (reveal t2))))
          (ensures  (is_stree r (Node (reveal t1) nd.value (reveal t2)) h)) = 
  ()
*)

let fresh_diff (s1 s2:Set.set nat) (h:heap) =
  forall r . (not (Set.mem r s1) /\ Set.mem r s2) ==> addr_unused_in r h


let rec lemma_unchanged (r:mtree) (t:stree) (s:Set.set nat) (h0 h1:heap)
  : Lemma (requires (Some? (wf r t h0) /\ 
                     Set.disjoint (Some?.v (wf r t h0)) s /\ 
                     modifies s h0 h1))
          (ensures  (wf r t h0 == wf r t h1)) (decreases t)
          [SMTPat (wf r t h0); SMTPat (modifies s h0 h1)]= 
  match t with
  | Leaf -> ()
  | Node t1 n t2 -> (
      let (Some nd) = sel h0 r in 
      lemma_unchanged nd.left t1 s h0 h1;
      lemma_unchanged nd.right t2 s h0 h1
    )


let rec insert (t:erased stree) (r:mtree) (n:nat) 
  : ST (erased stree) (requires (fun h0 -> is_stree r (reveal t) h0))
                      (ensures  (fun h0 t' h1 -> reveal t' = stree_insert (reveal t) n /\
                                                 is_stree r (reveal t') h1 /\ (
                                                 let (Some s) = wf r (reveal t) h0 in 
                                                 let (Some s') = wf r (reveal t') h1 in
                                                 modifies s h0 h1 /\
                                                 Set.subset s s' /\ 
                                                 fresh_diff s s' h0))) = 
  recall r;
  match !r with
  | None -> (
      let t1,r1 = create () in
      let t2,r2 = create () in  
      r := Some ({left = r1; value = n; right = r2});
      hide (Node (reveal t1) n (reveal t2)))
  | Some nd -> 
      if n = nd.value then t else
      if n < nd.value then (let t1 = hide (match (reveal t) with | Node t1 _ _ -> t1) in
                            let t2 = hide (match (reveal t) with | Node _ _ t2 -> t2) in
                            let h = get () in 
                            (*assert (let (Some s) = wf (nd.left) (reveal t1) h in Set.disjoint (only r) s);
                            assert (let (Some s) = wf (nd.right) (reveal t2) h in Set.disjoint (only r) s);
                            assert (let (Some s) = wf (nd.left) (reveal t1) h in 
                                    let (Some s') = wf (nd.right) (reveal t2) h in 
                                    Set.disjoint s s');*)
                            let t1' = insert t1 (nd.left) n in 
                            let h' = get () in 
                            assert (is_stree (nd.left) (reveal t1') h');
                            (*assert (let (Some s') = wf (nd.left) (reveal t1') h' in Set.disjoint (only r) s');*)
                            assert (let (Some s) = wf (nd.right) (reveal t2) h in
                                    let (Some s') = wf (nd.right) (reveal t2) h' in 
                                    s == s');
                            assert (is_stree (nd.right) (reveal t2) h');
                            //assert (Node (reveal t1') nd.value (reveal t2) = stree_insert (reveal t) n);
                            assert (sorted (Node (reveal t1') nd.value (reveal t2)));
                            
                            assume (sel h' r == Some ({ left=nd.left; value=nd.value; right=nd.right}));
                            //lemma_is_stree_node t1' t2 r nd.left nd.right nd.value h';
                            assume (is_stree r (Node (reveal t1') nd.value (reveal t2)) h');
                            admit ();
                            hide (Node (reveal t1') nd.value (reveal t2)))
                      else (admit ())


(* ------------------------------------------------------ *)

let test_create_insert_search () : St unit =
  let t1,r = create () in
  let t2 = insert t1 r 0 in
  let t3 = insert t2 r 1 in 
  let t4 = insert t3 r 2 in 
  let t5 = insert t4 r 0 in 
  let b1 = search t5 r 0 in
  let b2 = search t5 r 2 in
  let b3 = search t5 r 1 in
  let b4 = search t5 r 3 in
  let t6 = insert t5 r 3 in 
  let b5 = search t6 r 3 in
  let t1',r' = create () in
  let b6 = search t1' r' 0 in
  assert b1;
  assert b2;
  assert b3;
  assert (not b4);
  assert b5;
  assert (not b6)

