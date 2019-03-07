module CountST

open FStar.Ref

// BEGIN: count_st_aux
let rec count_st_aux (r:ref nat) (n:nat) 
  : ST unit (requires (fun _       -> True))
            (ensures  (fun h0 _ h1 -> modifies !{r} h0 h1 /\
                                     (* to ensure !{} in count_st *)
                                      sel h1 r == sel h0 r + n 
                                     (* sel h1 r == n would be wrong *))) =
  if n > 0 then (r := !r + 1; 
                 count_st_aux r (n - 1))
// END: count_st_aux

// BEGIN: count_st
let rec count_st (n:nat) 
  : ST nat (requires (fun _       -> True))
           (ensures  (fun h0 x h1 -> modifies !{} h0 h1 /\ x == n)) =
  let r = alloc 0 in 
  count_st_aux r n; 
  !r
// END: count_st
