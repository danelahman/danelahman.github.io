module RefinedStack

(*

  Exercise 3.

  In this exercise you will practice using refinement types to give functions precise enough types 
  that one doesn't need to worry about default cases that this precise typing rules out.

  The goal is to implement a refined variant of the stacks library that you developed in Exercise 2.
  Namely, recall that in Exercise 2 the return types of stack operations such as `pop` and `top` were 
  `option stack` and `option int`, rather than simply `stack` and `int`. This was because when we were 
  calling these operations, we did not whether the stack we got as an argument was empty or not. In 
  this exercise remedy this issue by assigning more precise (more refined) types to stack operations.

  Task 1: Modify the interface `RefinedStack.fsti`, assigning more precise (refinement) types to the 
          stack operations (`empty`, `push`, `pop`,  and `top`) for which one can feasibly provide a 
          concrete implementation. The important condition is that the return types of `pop` and `top` 
          have to be `stack` and `int` (without wrapping them in `option` or any other type former). 

  Task 2: Below, provide a concrete implementation of the interface given in `RefinedStack.fsti`.

          Hint: It will not look too different from what you already did in Exercise 2.

  Task 3: In `RefinedStackClient.fst`, observe that in its current state the client code does not 
          verify (depending on how much you added to `RefinedStack.fsti` in Task 1).

  Task 4: As in Exercise 2, to make `RefinedStackClient.fst` verify, expose additional properties 
          of stacks in `RefinedStack.fsti` and give proofs of these properties in the current file.

*)
