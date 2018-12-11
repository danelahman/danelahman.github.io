module SumST

open FStar.Ref
open FStar.Mul

(*

  Exercise 4.

  In this exercise you will practice writing and verifying stateful programs.

  The goal is to write and prove correct a stateful variant of the 1 + ... + n function 
  that we saw in Exercise 1, where we gave a purely functional definition of it. 

  Task 1: Give a more precise type to `sum_st_aux` so that `sum_st` verifies.

  Task 2: Provide a definition for the `sum_st_aux` function that verifies against 
          the type you gave it in Task 1, i.e., replace the `admit ()` with code.

          Hint 1: The type you gave `sum_st_aux` in Task 1 might not be strong enough 
          to act as a loop invariant for the recursive calls. So you might need to 
          revisit Task 1 and give `sum_st_aux` a stronger invariant-like type.

          Hint 2: For inspiration, see the `count_st` example on the lecture slides.
          
*)

let nth_triangular (n:nat) = ((n+1) * n) / 2

let rec sum_st_aux (r:ref nat) (n:nat) 
  : ST unit (requires (fun _ -> True))
            (ensures  (fun _ _ _ -> True)) = 
  admit ()

let rec sum_st (n:nat) 
  : ST nat (requires (fun _ -> True))
           (ensures  (fun h0 x h1 -> x = nth_triangular n /\ 
                                     modifies !{} h0 h1)) =
  let r = alloc 0 in 
  sum_st_aux r n; 
  !r
