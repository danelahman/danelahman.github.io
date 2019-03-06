module SwapRefsST

open FStar.Ref

// BEGIN: swap
val swap : r1:ref int -> r2:ref int -> 
  ST unit (requires (fun _       -> True))
          (ensures  (fun h0 _ h3 -> modifies !{r1,r2} h0 h3 /\
                                    sel h3 r2 == sel h0 r1 /\ 
                                    sel h3 r1 == sel h0 r2))
let swap r1 r2 =
  let t = !r1 in
  r1 := !r2;
  r2 := t
// END: swap
