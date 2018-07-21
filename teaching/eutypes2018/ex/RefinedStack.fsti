module RefinedStack

val stack : Type0  (* type of stacks *)

(* modify and implement this interface of refined stacks; the
   main requirement is that pop and top do not return option type *)

(* hint: compared to Stack.fsti and Stack.fst, you will need to 
         refine stack types below with the is_empty predicate;
         see the lemmas in Stack.fsti for inspiration *)

val is_empty : stack -> bool
val empty : stack
val push : int -> stack -> stack
val pop : stack -> stack
val top : stack -> int
