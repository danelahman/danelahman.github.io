module FactorialST

open FStar.Heap
open FStar.ST
open FStar.Mul

(*

  Exercise 5.

  In this exercise you will further practice writing and verifying stateful programs.

  The goal is to write a stateful variant of the factorial function and show that it 
  agrees with its purely functional definition which we saw on the lecture slides.

  Task 1: Give `factorial_st_aux` a more precise type so that you can remove the 
          [@expect_failure] attribute from `factorial_st` and show that it verifies.

  Task 2: Provide a definition for the `factorial_st_aux` function that verifies against 
          the type you gave it in Task 1, i.e., replace the `admit ()` with code.

          Hint: As in Exercise 4, the type you gave `factorial_st_aux` in Task 1 might not 
          be strong enough to act as a loop invariant for the recursive calls. So you 
          might need to revisit Task 1 and give it a stronger, invariant-like type.

*)

let rec factorial_tot (x:nat) : Tot nat = 
  if x = 0 then 1 else x * factorial_tot (x - 1)

let rec factorial_st_aux (r1 r2:ref nat) 
  : ST unit (requires (fun h0 -> True))
            (ensures  (fun h0 _ h1 -> True)) =
  admit ()

[@expect_failure]
let factorial_st (n:nat) 
  : ST nat (requires (fun _ -> True))
           (ensures  (fun h0 x h1 -> x = factorial_tot n /\
                                     modifies !{} h0 h1)) =
  let r1 = alloc n in
  let r2 = alloc 0 in 
  factorial_st_aux r1 r2;
  !r2
