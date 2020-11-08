module FactorialST

open FStar.Heap
open FStar.ST
open FStar.Mul

(*

  Exercise 5.

  In this exercise you will further practice writing and verifying stateful programs.

  The goal is to write a stateful variant of the factorial function and show that it 
  agrees with its purely functional definition which we saw on the lecture slides.

  Task 1: Give `factorial_st_aux` a more precise type so that `factorial_st` verifies.

  Task 2: Provide a definition for the `factorial_st_aux` function that verifies against 
          the type you gave it in Task 1, i.e., replace the `admit ()` with code.

          Hint: As in Exercise 4, the type you gave `factorial_st_aux` in Task 1 might not 
          be strong enough to act as a loop invariant for the recursive calls. So you 
          might need to revisit Task 1 and give it a stronger, invariant-like type.

*)

let rec factorial_tot (x:nat) : GTot nat = 
  if x = 0 then 1 else x * factorial_tot (x - 1)

let rec factorial_st_aux (r1 r2:ref nat) 
  : ST unit (requires (fun h0 -> addr_of r1 <> addr_of r2))
            (ensures  (fun h0 _ h1 -> sel h1 r2 = factorial_tot (sel h0 r1) /\
                                      sel h1 r1 = 0 /\
                                      modifies !{r1,r2} h0 h1)) =
  let x1 = !r1 in
  if x1 = 0
  then r2 := 1
  else 
    (r1 := x1 - 1;
     factorial_st_aux r1 r2;
     r2 := !r2 * x1)

let factorial_st (n:nat) : ST nat (requires (fun _ -> True))
                                  (ensures  (fun h0 x h1 -> x = factorial_tot n /\
                                                            modifies !{} h0 h1)) =
  let r1 = alloc n in
  let r2 = alloc 0 in 
  factorial_st_aux r1 r2;
  !r2
