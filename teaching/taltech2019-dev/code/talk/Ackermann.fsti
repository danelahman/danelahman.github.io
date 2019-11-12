module Ackermann

(* The type signature for the standard Ackermann function. 

   Importantly, as this function is given the 'Tot' effect, 
   the definition in Ackermann.fst has to be a total function. *)

val ackermann: m:nat -> n:nat -> Tot nat
