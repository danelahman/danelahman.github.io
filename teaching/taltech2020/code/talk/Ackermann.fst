module Ackermann

(* This standard vairant of the Ackermann function is exposed by
   Ackermann.fsti; see Ackermann.fsti for its type signature.    *)

let rec ackermann m n = 
  if m = 0 then n + 1
  else if n = 0 then ackermann (m - 1) 1
  else ackermann (m - 1) (ackermann m (n - 1))




(* The following variant of the Ackermann function with swapped
   arguments is not exposed by the interface file Ackermann.fsti. 
   
   Note that we need to additionally instruct the typechecker 
   which termination metric to use (the default implicit is the 
   left-to-right lexicographic ordering of non-function arguments). *)

val swapped_ackermann: n:nat -> m:nat -> Tot nat (decreases %[m;n])

let rec swapped_ackermann n m = 
  if m = 0 then n + 1
  else if n = 0 then swapped_ackermann 1 (m - 1)
  else swapped_ackermann (swapped_ackermann (n - 1) m) (m - 1)



val swapped_ackermann_bad: n:nat -> m:nat -> Tot nat

(* Attribute telling the typechecker that this definition must not verify. *)
[@expect_failure] 
let rec swapped_ackermann_bad n m = 
  if m = 0 then n + 1
  else if n = 0 then swapped_ackermann_bad 1 (m - 1)
  else swapped_ackermann_bad (swapped_ackermann_bad (n - 1) m) (m - 1)




(* Finally, here is a lemma showing that the two Ackermann variants agree. *)

val lemma_ackermanns_equal : m:nat -> n:nat -> Lemma (ackermann m n = swapped_ackermann n m)

let rec lemma_ackermanns_equal m n =  
  if m = 0 then ()
  else if n = 0 then lemma_ackermanns_equal (m - 1) 1
  else (lemma_ackermanns_equal m (n - 1);
        lemma_ackermanns_equal (m - 1) (ackermann m (n - 1)))
