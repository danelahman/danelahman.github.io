module Decreases

open FStar.List

[@expect_failure]
let rec foo (l:list nat) : Tot (list nat) =
  match l with
  | [] -> []
  | [n] -> [n]
  | n::m::l' -> m::foo (n::l')

let rec bar (l:list nat) : Tot (list nat) (decreases (length l)) =
  match l with
  | [] -> []
  | [n] -> [n]
  | n::m::l' -> m::bar (n::l')
