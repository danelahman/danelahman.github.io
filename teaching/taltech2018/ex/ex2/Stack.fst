module Stack

(*

   Exercise 2.

   In this exercise you will practice writing purely functional programs against interfaces.

   The goal is for you to define a small library of integer-valued stacks (if you haven't 
   seen stacks before, see e.g. https://en.wikipedia.org/wiki/Stack_(abstract_data_type)), 
   and use it in the client code in `StackClient.fst`, including verifying simple properties.

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
