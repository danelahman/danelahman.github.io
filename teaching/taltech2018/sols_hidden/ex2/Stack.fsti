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

val lemma_push_is_not_empty : s:stack -> i:int ->
  Lemma (~(is_empty (push i s))) [SMTPat (is_empty (push i s))]

val lemma_is_not_empty_top_some : s:stack{~(is_empty s)} -> 
  Lemma (Some? (top s)) [SMTPat (top s)]

val lemma_is_not_empty_pop_some : s:stack{~(is_empty s)} -> 
  Lemma (Some? (pop s)) [SMTPat (pop s)]

val lemma_push_top : s:stack -> i:int -> 
  Lemma (Some? (top (push i s)) /\ Some?.v (top (push i s)) = i) 
  [SMTPat (top (push i s))]
                                                  
val lemma_push_pop : s:stack -> i:int -> 
  Lemma (Some? (pop (push i s)) /\ Some?.v (pop (push i s)) == s) 
  [SMTPat (pop (push i s))]

val lemma_top_pop_push : s:stack{~(is_empty s)} ->  
  Lemma (push (Some?.v (top s)) (Some?.v (pop s)) == s)
