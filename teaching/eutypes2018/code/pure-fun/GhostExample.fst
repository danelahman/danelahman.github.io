module GhostExample

[@expect_failure]
let f1 (g:unit -> GTot nat) : n:nat{n = g ()} = g ()

[@expect_failure]
let f2 (g:unit -> Dv nat) : n:nat{n = g ()} = g ()

let f3 (g:unit -> GTot (n:nat{n = 4})) : n:nat{n = g ()} = 4
