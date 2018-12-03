module Stack

(*

   Exercise 2.

   See `Stack.fst` for details.

*)

val stack : Type0

val empty : stack

val is_empty : stack -> GTot bool

val push : int -> stack -> stack

val pop : stack -> option stack

val top : stack -> option int

val lemma_empty_is_empty : unit -> Lemma (is_empty (empty))
