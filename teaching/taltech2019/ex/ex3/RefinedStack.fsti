module RefinedStack

(*

  Exercise 3.

  See `RefinedStack.fst` for details.

*)

val stack : Type0

val is_empty : stack -> GTot bool

val empty : stack

val push : int -> stack -> stack

val pop : stack -> stack           

val top : stack -> int
