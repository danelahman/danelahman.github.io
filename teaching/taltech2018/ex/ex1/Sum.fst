module Sum

open FStar.Mul

(* 

  Exercise 1.

  In this exercise you will practice defining recursive functions and doing proofs about them
     
  Task 1: Define a recursive total function `sum` that sums up natural numbers from 1 to n.
          That is, replace the 1st `admit ()` with an appropriate recursive definition.

  Task 2: Prove that `sum` is equal to the nth triangual number (as computed by `nth_triangular`).
          That is, replace the 2nd `admit ()` with a proof of `sum n = nth_triangular n`.
         
*)


let rec sum (n:nat) : Tot nat = admit ()

let nth_triangular (n:nat) : GTot nat = ((n+1) * n) / 2

let rec sum_correct (n:nat) : Lemma (sum n = nth_triangular n) = admit ()
