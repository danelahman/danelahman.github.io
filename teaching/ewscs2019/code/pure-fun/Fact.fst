module Fact

open FStar.Mul

let nat = i:int{i >= 0}

val factorial: nat -> Tot nat
let rec factorial n 
  = if n = 0 then 1 else n * (factorial (n - 1))
