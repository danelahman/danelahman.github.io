module AppendLength

open FStar.List.Tot.Base

// BEGIN: append
let rec append (#a:Type) (xs ys : list a) : Tot (list a) = 
  match xs with
  | []       -> ys
  | x :: xs' -> x :: append xs' ys
// END: append

// BEGIN: append_length
let rec append_length (#a:Type) (xs ys : list a) 
  : Pure unit
      (requires True)
      (ensures  (fun _ -> length (append xs ys) = length xs + length ys))
      
= match xs with
  | []       -> ()          
  (* nil-VC:  len (app [] ys) = len [] + len ys *)
  (* nil-VC': len ys = 0 + len ys               *)
  | x :: xs' -> append_length xs' ys
  (* cons-VC:  len (app (x::xs') ys) = len (x::xs') + len ys *)                
  (* cons-VC': 1 + len (app xs' ys) = (1 + len xs') + len ys *)
// END: append_length

// BEGIN: append_length_lemma
let rec append_length_lemma (#a:Type) (xs ys : list a) 
    : Lemma (length (append xs ys) = length xs + length ys)    
= match xs with
  | []       -> ()
  | x :: xs' -> append_length_lemma xs' ys
// END: append_length_lemma
