module AckermannSwapped

val swapped_ackermann_bad: n:nat -> m:nat -> Tot nat
[@expect_failure] 
let rec swapped_ackermann_bad n m = 
  if m = 0 then n + 1
  else if n = 0 then swapped_ackermann_bad 1 (m - 1)
  else swapped_ackermann_bad (swapped_ackermann_bad (n - 1) m) (m - 1)

val swapped_ackermann: n:nat -> m:nat -> Tot nat (decreases %[m;n])
let rec swapped_ackermann n m = 
  if m = 0 then n + 1
  else if n = 0 then swapped_ackermann 1 (m - 1)
  else swapped_ackermann (swapped_ackermann (n - 1) m) (m - 1)
