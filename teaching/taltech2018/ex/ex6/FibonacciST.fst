module FibonacciST

open FStar.Ref

(*

  Exercise 6.

  In this exercise you will further practice writing and verifying stateful programs.

  The goal is to write a stateful, tail-recursive variant of the Fibonacci function and 
  show that it agrees with its purely functional non-tail-recursive definition.

  (If you haven't seen Fibonacci before, see https://en.wikipedia.org/wiki/Fibonacci_number)

  Task 1: Give `fibonacci_st_aux` a more precise type so that `fibonacci_st` verifies.

  Task 2: Provide a definition for the `fibonacci_st_aux` function that verifies against 
          the type you gave it in Task 1, i.e., replace the `admit ()` with code.

          Hint 1: As in Exercises 4,5, the type you gave `factorial_st_aux` in Task 1 might 
          not be strong enough to act as a loop invariant for the recursive calls. So you 
          might need to revisit Task 1 and give it a stronger, invariant-like type.

          Hint 2: The function `fibonacci_st_aux` will work similarly to the iterative 
          solution `itfib` to computing Fibonacci numbers that you saw in Lecture 8 of this 
          course, the difference being that here we use mutable references for accumulators.

          Hint 3: In the function function `fibonacci_st_aux`, the variable `i` counts 
          in which iteration the function is at the moment between 1 and n. Thus the 
          tail-recursive definition you write will very much behave like a for-loop.

*)

let rec fibonacci_tot (n:nat) : GTot nat 
  = if n <= 1 then 1 else fibonacci_tot (n - 1) + fibonacci_tot (n - 2)

let rec fibonacci_st_aux (i:pos) (n:nat) (r1 r2:ref nat) 
  : ST unit (requires (fun _ -> True))
            (ensures  (fun _ _ _ -> True)) =
  admit ()

let fibonacci_st (n:nat) 
  : ST nat (requires (fun _ -> True))
           (ensures  (fun h0 x h1 -> x = fibonacci_tot n /\ 
                                     modifies !{} h0 h1)) =
  if n <= 1 then 1
            else (let r1 = alloc 1 in
                  let r2 = alloc 1 in
                  fibonacci_st_aux 1 n r1 r2;
                  !r2)
