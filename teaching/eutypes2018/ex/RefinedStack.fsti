module RefinedStack

val stack : Type0  (* type of stacks *)

(* exercise: modify and implement this interface of refined stacks; the main
             requirement is that *pop* and *top* must not return in the option type *)

(* hint: compared to Stack.fsti and Stack.fst, you will need to 
         refine stack types below with the is_empty predicate *)

val empty : stack
val is_empty : stack -> GTot bool

val push : int -> stack -> stack
val pop : stack -> stack                (* before the return type was `option stack`*)
val top : stack -> int                  (* before the return type was `option int` *)
