module RefinedStack

val stack : Type0  (* type of stacks *)

val is_empty : stack -> bool
val empty : stack
val push : int -> stack -> stack
val pop : stack -> stack
val top : stack -> int
