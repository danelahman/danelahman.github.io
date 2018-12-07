module BinarySearchTreeClient

open FStar.ST

open BinarySearchTree

(* Client code to test mutable binary search trees in BinarySearchTree *)

#set-options "--max_ifuel 0"

[@expect_failure]
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
  let t2' = insert t1' r' 4 in
  let b7 = search t2' r' 4 in

  let b8 = search t6 r 5 in
  let t7 = insert t6 r 6 in 
  let b9 = search t7 r 5 in
  let b10 = search t7 r 6 in
  let b11 = search t7 r 1 in 

  assert (t4 == t5);

  assert b1;
  assert b2;
  assert b3;
  assert (not b4);
  assert b5;
  assert (not b6);
  assert b7;
  assert (not b8);
  assert (not b9);
  assert b10;
  assert b11
