module Heap

(** A very simplified fragment of F*'s flat garbage collected heap model **)

(* Heaps *)

val heap : Type u#1

(* References *)

val ref (a:Type0) : Type0

val addr_of: #a:Type0 -> ref a -> GTot nat

val contains: #a:Type0 -> heap -> ref a -> Type0

(* Select *)

val sel_tot: #a:Type0 -> h:heap -> r:ref a{h `contains` r} -> Tot a

val sel: #a:Type0 -> heap -> ref a -> GTot a

(* Update *)

val upd_tot: #a:Type0 -> h:heap -> r:ref a{h `contains` r} -> x:a -> Tot heap

val upd: #a:Type0 -> h:heap -> r:ref a -> x:a -> GTot heap

(* Some natural lemmas *)

val lemma_sel_upd1 (#a:Type0) (h:heap) (r1:ref a) (x:a) (r2:ref a)
  :Lemma (requires (addr_of r1 = addr_of r2))
         (ensures  (sel (upd h r1 x) r2 == x))
         [SMTPat (sel (upd h r1 x) r2)]

val lemma_sel_upd2 (#a:Type0) (#b:Type0) (h:heap) (r1:ref a) (r2:ref b) (x:b)
  :Lemma (requires (addr_of r1 <> addr_of r2))
         (ensures  (sel (upd h r2 x) r1 == sel h r1))
	 [SMTPat (sel (upd h r2 x) r1)]

