module RefinedStack

val stack : Type0  (* type of stacks *)

(* modify and implement this interface of refined stacks; the main
   requirement is that *pop* and *top* must not return in option type *)

(* hint: compared to Stack.fsti and Stack.fst, you will need to 
         refine stack types below with the is_empty predicate *)

val empty : stack
val is_empty : stack -> bool

val push : int -> stack -> stack
val pop : stack -> stack                (* before was option stack*)
val top : stack -> int                  (* before was option int *)
