module Heap
  open FStar.TSet

// BEGIN: heap_model
  val heap : Type
  val ref : Type -> Type

  val sel : #a:Type -> heap -> ref a -> GTot a       (* in ghost effect, meaning this *)
  val addr_of: #a:Type -> ref a -> GTot nat          (* code can only be used in specs *)

  let modifies (s:set nat) (h0 h1 : heap) =
    forall (a:Type) (r:ref a).{:pattern (sel h1 r)}
        ~(addr_of r `mem` s) ==> sel h1 r == sel h0 r
// END: heap_model
