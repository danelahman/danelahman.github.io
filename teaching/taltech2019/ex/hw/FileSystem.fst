module FileSystem

(* Task1: Define the type of well-formed paths as lists of strings 
          (i.e., raw paths) that do not contain nodes with empty 
          names. In other words, replace the proposition `True`
          with a predicate on `p` that ensures this property. *)

type path = p:list string{True}

(* Type of file systems *)

type fs_tree =
  | Node : list (string * fs_tree) -> fs_tree

(* An effect that characterises programs that use the file system. *)

let fs_st (a:Type) = fs_tree -> M (a * fs_tree)

let return_fs_st (a:Type) (x:a) : fs_st a 
  = fun fs0 -> (x,fs0)

let bind_fs_st (a:Type) (b:Type) (f:fs_st a) (g:a -> fs_st b) : fs_st b
  = fun fs0 -> let (x,fs1) = f fs0 in 
              g x fs1

let read_st () : fs_st fs_tree 
  = fun fs0 -> (fs0,fs0)

let write_st (fs:fs_tree) : fs_st unit 
  = fun _ -> ((), fs)

total new_effect {
  FileSystem : a:Type -> Effect
  with repr     = fs_st
     ; bind     = bind_fs_st
     ; return   = return_fs_st
     ; read     = read_st
     ; write    = write_st
}

(* Task2: Define a well-formedness predicate for file systems. As in your regular 
          coursework, a file system is well-formed when identical paths cannot 
          lead to different nodes in the tree. *)

let fs_tree_wf (fs:fs_tree) : bool = 
  admit ()

let wf_fs_tree = fs:fs_tree{fs_tree_wf fs}

(* Pre- and postcondition variant of the `FileSystem` effect, which additionally 
   assumes that the initial file system (`fs0`) is well-formed and additionally 
   requires one to prove that the final file system (`fs1`) is still well-formed.*)

effect FS (a:Type) 
          (pre:fs_tree -> Type0) 
          (post:fs_tree -> a -> fs_tree -> Type0) = 
  FileSystem a (fun fs0 p -> 
                 pre fs0 /\ 
                 fs_tree_wf fs0 /\ 
                 (forall x fs1 . (post fs0 x fs1 /\ fs_tree_wf fs1) ==> p (x,fs1)))

(* Effectful actions to read and update the file system in your code below. *)

let read (_:unit) : FS wf_fs_tree
                       (requires (fun _ -> True)) 
                       (ensures (fun fs0 fs fs1 -> fs0 == fs /\ fs == fs1)) = 
  FileSystem?.read ()

let write (fs:wf_fs_tree) : FS unit 
                               (requires (fun _ -> True)) 
                               (ensures (fun _ _ fs1 -> fs1 == fs)) = 
  FileSystem?.write fs

(* Task3: Define a function in the `FS` effect that creates a new directory in the file system. 

   Hint: As part of defining `create_dir`, you also need to prove that creating a well-formed 
         path in a well-formed tree results in a well-formed tree. 

   Task3.Bonus: What additional properties could one prove about the `create_dir` function?
                Try extending the (currently trivial) specification of `create_dir` with 
                these properties and prove that your implementation indeed satisfies them.

   Hint: Think about the shape of the file system after a new path has been created.
         
*)

let create_dir (p:path) : FS unit 
                             (requires (fun fs0 -> True)) 
                             (ensures  (fun fs0 _ fs1 -> True)) = 
  admit ()

(*  *)


(*
let state = int

let st (a:Type) = state -> M (a * state)

let return_st (a:Type) (x:a) : st a 
  = fun s0 -> (x,s0)

let bind_st (a:Type) (b:Type) (f:st a) (g:a -> st b) : st b
  = fun s0 -> let (x,s) = f s0 in 
              g x s

let get () : st state 
  = fun s0 -> (s0,s0)

let put (x:state) : st unit 
  = fun s0 -> ((), x)

total reifiable reflectable new_effect {
  STATE : a:Type -> Effect
  with repr     = st
     ; bind     = bind_st
     ; return   = return_st
     ; get      = get
     ; put      = put
}

#reset-options

effect St (a:Type) = STATE a (fun _ p -> forall x s1 . p (x,s1))

(**********************************************************
 *                                                        *
 * Proof of stateful summing using reification            *
 *                                                        *
 **********************************************************)

open FStar.Mul

let sum_tot (n:nat) = ((n+1) * n) / 2

(* Exercise1: give a definition of sum_st using the St effect defined above *)

let rec sum_st (n:nat) : St unit
= admit()

(* Exercise2: prove that sum_st agrees with sum_tot by using monadic reification *)

let lemma_sum_st (n:nat) (s:state) 
  : Lemma (True)
= admit()

*)
