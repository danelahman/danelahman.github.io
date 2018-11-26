module Ackermann

(* val ackermann: m:nat -> n:nat -> Tot nat *)

let rec ackermann m n = 
  if m = 0 then n + 1
  else if n = 0 then ackermann (m - 1) 1
  else ackermann (m - 1) (ackermann m (n - 1))
