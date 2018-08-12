module InitFreezeArrayMST

open FStar.Preorder
open FStar.Heap
open FStar.ST
open FStar.MRef

open FStar.List.Tot

let rec lkp (#a:Type) (l:list a) (i:nat{i < length l}) : a = 
  match l with 
  | hd::tl -> if i = 0 then hd else lkp tl (i - 1)

let rec upd (#a:Type) (l:list a) (i:nat{i < length l}) (v:a) : l':list a{length l == length l'} = 
  match l with 
  | hd::tl -> if i = 0 then v::tl else hd::(upd tl (i-1) v)
  
type astate (a:Type) (n:nat) =
  | Empty   : l:list (option a){length l = n /\ for_all None? l} -> astate a n
  | Mutable : l:list (option a){length l = n } -> astate a n
  | Frozen  : l:list (option a){length l = n /\ for_all Some? l}  -> astate a n

let evolve' (a:Type) (n:nat) = fun (a1 a2:astate a n) ->
  match a1 , a2 with
  | Empty _   , _
  | Mutable _ , Mutable _
  | Mutable _ , Frozen _    -> True 
  | Frozen a1' , Frozen a2' -> a1' == a2'
  | _         , _           -> False
let evolve (a:Type) (n:nat) : Tot (preorder (astate a n)) = evolve' a n

let aref (a:Type) (n:nat) : Type = mref (astate a n) (evolve a n)

let rec create_empty (a:Type) (n:nat) : xs:list (option a){length xs = n /\ for_all None? xs } = 
  match n with
  | 0 -> []
  | n -> let xs' = create_empty a (n - 1) in None :: xs'

let alloc (a:Type) (n:nat) = 
  alloc #_ #(evolve a n) (Empty (create_empty a n))

let read (#a:Type) (#n:nat) (r:aref a n) (i:nat{i < n})
  : ST a (requires (fun h0 -> match (sel h0 r) with 
                              | Empty   _ -> False
                              | Mutable l
                              | Frozen  l -> Some? (lkp l i)))
         (ensures  (fun h0 x h1 -> h0 == h1 /\
                                   (match (sel h1 r) with
                                    | Mutable l
                                    | Frozen  l -> x == Some?.v (lkp l i))))
  = match (!r) with
    | Mutable l 
    | Frozen  l -> Some?.v (lkp l i)

let write (#a:Type) (#n:nat) (r:aref a n) (v:a) (i:nat{i < n}) 
  : ST unit (requires (fun h0 -> ~(Frozen? (sel h0 r))))
            (ensures  (fun h0 x h1 -> modifies !{r} h0 h1 /\
                                      (match (sel h0 r) with 
                                       | Empty   l 
                                       | Mutable l -> sel h1 r == Mutable (upd l i (Some v)))))
= match (!r) with
  | Empty l    
  | Mutable l -> r:= Mutable (upd l i (Some v))


let freeze (#a:Type) (#n:nat) (r:aref a n) 
  : ST unit (requires (fun h0 -> Mutable? (sel h0 r) /\ 
                                 for_all Some? (Mutable?.l (sel h0 r))))
            (ensures  (fun h0 x h1 -> modifies !{r} h0 h1 /\
                                      Frozen? (sel h1 r) /\
                                      Frozen?.l (sel h1 r) == Mutable?.l (sel h0 r)))
= match (!r) with
  | Mutable l -> r := Frozen l

(*
assume val complex_procedure (r:eref int) : St unit

let main() : St unit =
  let r = alloc int in
  (* ignore (read r) -- fails like it should *)
  write r 42;
  ignore (read r);                                    (* needs --use_two_phase_tc true *)
  write r 0;
  witness_token r (fun rs -> ~(Empty? rs));
  freeze r;
  (* write r 7; -- fails like it should *)
  ignore (read r);
  witness_token r (fun rs -> rs == Frozen 0);
  complex_procedure r;
  (* ignore (read r); -- fails like it should *)
  recall_token r (fun rs -> ~(Empty? rs));
  let x = read r in
  (* assert (x == 0) -- fails like it should *)
  recall_token r (fun rs -> rs == Frozen 0);
  assert (x == 0)
*)
