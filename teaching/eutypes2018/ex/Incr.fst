module Incr

val incr : x:int -> Tot (y:int{x < y})
let incr x = x + 1
