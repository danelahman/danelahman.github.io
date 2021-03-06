module Stack

(*

   Exercise 2.

   In this exercise you will practice writing purely functional programs against interfaces.

   The goal is for you to define a small library of integer-valued stacks and use it in the 
   client code in `StackClient.fst`, including verifying simple properties of such stacks.

   If you haven't seen stacks before, see e.g. https://en.wikipedia.org/wiki/Stack_(abstract_data_type)

   Task 1: In the space below, define all the types, functions, and lemmas required by the  
           interface `Stack.fsti` so that the current file (`Stack.fst`) verifies.

           Note: When using the interactive fstar-mode, F* will not complain if you haven't
           defined all the functions and lemmas required by `Stack.fsti` (but it will 
           complain if you define them in different order than stated in `Stack.fsti`). 
           The former is so because of the interactive nature of using fstar-mode, and the 
           possibility of extending the interface and the implementation code in parallel.
           Thus, to ensure that your implementation of stacks truly reflects the interface, 
           you should run F* from the command line with `fstar.exe` on the current file.

   Task 2: Try to verify `StackClient.fst`. The verification will fail because `StackClient.fst` 
           cannot see the implementation details of `Stack.fst` not exposed by its interface. 

   Task 3: To overcome the failure in Task 2, extend the interface `Stack.fsti` with 
           additional properties (lemmas) about the behaviour of stacks, and of course 
           prove the validity of these additional properties in the current file (`Stack.fst`).
           Add as many lemmas as needed to get the client code (`StackClient.fst`) to verify. 

           Hint: To get `StackClient.fst` to verify without having to call these extra lemmas
           explicitly in `main ()`, you need to annotate them with SMT-patterns ([SMTPat (...)]).

*)

let stack = list int
  
let empty = []

let is_empty xs = match xs with
                  | [] -> true
                  | x::xs' -> false

let push x xs = x :: xs

let pop xs = match xs with
             | [] -> None
             | x::xs' -> Some xs'

let top xs = match xs with
             | [] -> None
             | x::xs' -> Some x

let lemma_empty_is_empty () = ()

let lemma_push_is_not_empty s i = ()

let lemma_is_not_empty_top_some s = ()

let lemma_is_not_empty_pop_some s = ()

let lemma_push_top s i = ()

let lemma_push_pop s i = ()

let lemma_top_pop_push s = ()
