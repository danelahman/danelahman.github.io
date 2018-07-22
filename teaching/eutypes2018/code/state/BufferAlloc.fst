module BufferAlloc

module B = LowStar.Buffer

open LowStar.BufferOps
open FStar.HyperStack.ST
open FStar.UInt64

let f (): Stack UInt64.t (requires (fun _ -> True))
                         (ensures  (fun _ _ _ -> True))
  = push_frame ();
    let b = B.alloca 0UL 64ul in
    assert (b.(0ul) == 0UL);
    b.(0ul) <- b.(0ul) +^ 32UL;
    let r = b.(0ul) in
    pop_frame ();
    assert (r == 32UL);
    r
