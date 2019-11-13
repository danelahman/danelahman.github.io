module RefinedStackClient

open RefinedStack

(*

  Exercise 3.

  See `RefinedStack.fst` for details.

*)

let main() =
  let s0 = empty (* <: stack *) in

  assert (is_empty s0);

  let s1 = push 3 s0 (* <: stack *) in
  assert (~(is_empty s1));

  let s2 = push 4 s1 (* <: stack *) in
  assert (~(is_empty s2));

  let i = top s2 (* <: int *) in
  assert (i = 4);

  let s3 = pop s2 (* <: stack *) in
  assert (s3 == s1);

  let j = top s3 in
  assert (j = 3)

