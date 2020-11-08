module Heap

(** A very simplified fragment of F*'s flat garbage collected heap model **)

(* Heaps *)

private noeq type heap_rec = {
  next_addr: nat;
  memory   : nat -> option (a:Type0 & a)
}

let heap = h:heap_rec{(forall (n:nat). n >= h.next_addr ==> None? (h.memory n))}

(* References *)

private noeq type ref' (a:Type0) :Type0 = {
  addr: nat;
  init: a;
}

let ref a = ref' a

let addr_of #a r = r.addr

let contains #a h r =
  let _ = () in
  Some? (h.memory r.addr) /\
  (let Some (| a1, _ |) = h.memory r.addr in a == a1)

(* Select *)

let sel_tot #a h r =
  let Some (| _, x |) = h.memory r.addr in
  x

let sel #a h r =
  if FStar.StrongExcludedMiddle.strong_excluded_middle (h `contains` r) then
    sel_tot #a h r
  else r.init

(* Update *)

let upd_tot' (#a: Type0) (h: heap) (r: ref a) (x: a) =
  { h with memory = fun r' -> if r.addr = r'
			      then Some (| a, x |)
                              else h.memory r' }

let upd_tot #a h r x = upd_tot' h r x

let upd #a h r x =
  if FStar.StrongExcludedMiddle.strong_excluded_middle (h `contains` r)
  then upd_tot' h r x
  else
    if r.addr >= h.next_addr
    then
      { next_addr = r.addr + 1;
        memory    = fun r' -> if r' = r.addr
	   		      then Some (| a, x |)
                              else h.memory r' }
    else
      { h with memory = fun r' -> if r' = r.addr
				  then Some (| a, x |)
                                  else h.memory r' }

(* Some natural lemmas *)

let lemma_sel_upd1 #a h r1 x r2 = ()
let lemma_sel_upd2 #a #b h r1 r2 x = ()
