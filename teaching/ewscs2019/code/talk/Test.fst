module Test

type vec (a:Type) : nat -> Type =
  | Nil  : vec a 0
  | Cons : #n:nat -> hd:a -> tl:vec a n -> vec a (n + 1)

let rec map (#n:nat) (#a #b:Type) (f:a -> b) (as:vec a n) : vec b n =
  match as with
  | Nil        -> Nil
  | Cons hd tl -> Cons (f hd) (map f tl)

let rec lookup #a #n (as:vec a n) (i:nat{i < n}) : a = 
  match as with
  | Cons hd tl -> if i = 0 then hd else lookup tl (i - 1)

let rec length #a (as:list a) : nat =
  match as with
  | []    -> 0
  | _ :: tl -> 1 + length tl

let rec lookup' #a (as:list a) (i:nat{i < length as}) : a = 
  match as with
  | hd :: tl -> if i = 0 then hd else lookup' tl (i - 1)
