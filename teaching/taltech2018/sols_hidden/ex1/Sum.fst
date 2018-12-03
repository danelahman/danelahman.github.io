module Sum

open FStar.Mul

(* 

  Exercise 1: 
   
     1.1 Define a recursive total function `sum` that sums up natural numbers from 1 to n

     1.2 Prove that `sum` is equal to the nth triangual number (as computed by `triangular`)
     
*)


let rec sum (n:nat) : Tot nat = 
  if n > 0 then n + sum (n-1) else 0

let triangular (n:nat) : GTot nat = 
  ((n+1) * n) / 2

let rec sum_correct (n:nat) : Lemma (sum n = triangular n) =
  if n > 0 then sum_correct (n-1)
