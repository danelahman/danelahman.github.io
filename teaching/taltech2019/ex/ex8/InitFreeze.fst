module InitFreeze

open FStar.Preorder
open FStar.Heap
open FStar.ST
open FStar.MRef

(*

  Exercise 8.

  In this exercise you practice how to use one of the main forms of monotonic state used 
  in F*, namely, monotonic references and witnessing/recalling stable properties. 

  The goal is to implement a refinement of memory references that can be in three (ghost) 
  states: Empty, Mutable, or Frozen. The idea is that when one creates such references, 
  they are initially in the Empty state, then when we write value(s) into them, they 
  become Mutable, and finally we can mark them as Frozen, which  means that it is forbidden 
  to write to such references (i.e., change their values) from thereon.

*)

(*

  The (ghost) state of initializable-freezable references (as described above).

*)

type rstate (a:Type) =
  | Empty : rstate a
  | Mutable : v:a -> rstate a
  | Frozen : v:a -> rstate a

(*

  Task 1: Define a preorder on the (ghost) states of initializable-freezable references that
          describes how the (ghost) state is allowed to evolve (as per above discussion).

*)
  
let evolve (a:Type) : Tot (preorder (rstate a)) = 
  admit ()

(*

  Initializable-freezable references are monotonic references with the above preorder.

*)

let eref (a:Type) : Type = mref (rstate a) (evolve a)

(*

  Task 2: Define the allocation operation for initializable-freezable references. 

          Hint: You will need to strengthen the specification to verify `main()` below 
          so that it matches with the informal description of such references above.

*)

let alloc (a:Type) : ST (eref a) (requires (fun h0 -> True))
                                 (ensures  (fun h0 r h1 -> True)) = 
  admit ()

(*

  Task 3: Define the read operation for initializable-freezable references.

          Hint: You will need to strengthen the specification to verify `main()` below 
          so that it matches with the informal description of such references above.

*)

let read (#a:Type) (r:eref a) 
  : ST a (requires (fun h0 -> True))
         (ensures  (fun h0 v h1 -> True)) = 
  admit ()

(*

  Task 4: Define the write operation for initializable-freezable references.

          Hint: You will need to strengthen the specification to verify `main()` below 
          so that it matches with the informal description of such references above.

*)

let write (#a:Type) (r:eref a) (v:a) :
      ST unit (requires (fun h0 -> True))
              (ensures  (fun h0 _ h1 -> True)) = 
  admit ()

(*

  Task 5: Define the freeze operation for initializable-freezable references.

          Hint: You will need to strengthen the specification to verify `main()` below 
          so that it matches with the informal description of such references above.

*)

let freeze (#a:Type) (r:eref a) :
      ST unit (requires (fun h0 -> True))
              (ensures  (fun h0 _ h1 -> True)) = 
  admit ()

(*

  Task 6: If you have defined the specifications and code above correctly, you will 
          be able to verify the client code in `main()` below. But if you uncomment 
          any of the four commented out commands, `main()` must fail to verify.

*)

assume val complex_procedure (r:eref int) : St unit

let main() : St unit =
  let r = alloc int in
  (* ignore (read r) -- fails like it should *)
  write r 42;
  ignore (read r);
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
