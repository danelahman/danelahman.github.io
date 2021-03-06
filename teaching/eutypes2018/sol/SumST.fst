module SumST

open FStar.Ref
open FStar.Mul

let sum_tot (n:nat) = ((n+1) * n) / 2

let rec sum_st' (r:ref nat) (n:nat) 
  : ST unit (requires (fun _ -> True))
            (ensures  (fun h0 _ h1 -> sel h1 r == sel h0 r + sum_tot n /\
                                      modifies !{r} h0 h1)) = 
  if n > 0 then (r := !r + n; 
                 sum_st' r (n-1))

let rec sum_st (n:nat) 
  : ST nat (requires (fun _ -> True))
           (ensures  (fun h0 x h1 -> x == sum_tot n /\ 
                                     modifies !{} h0 h1)) =
  let r = alloc 0 in 
  sum_st' r n; 
  !r
