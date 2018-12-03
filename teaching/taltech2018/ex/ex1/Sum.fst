module Sum

open FStar.Mul

(* 

  Exercise 1: 
   
     1.1 Define a recursive total function `sum` that sums up natural numbers from 1 to n.
         (That is, replace the 1st `admit ()` with an appropriate recursive definition.)

     1.2 Prove that `sum` is equal to the nth triangual number (as computed by `triangular`).
         (That is, replace the 2nd `admit ()` with a proof of `sum n = triangular n`.)
         
*)


let rec sum (n:nat) : Tot nat = 
  admit ()

let nth_triangular (n:nat) : GTot nat = 
  ((n+1) * n) / 2

let rec sum_correct (n:nat) : Lemma (sum n = nth_triangular n) =
  admit ()
