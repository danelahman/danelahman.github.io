module FileSystem

(* Task 1: Define the type of well-formed paths as lists of strings 
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

(* Task 2: Define a well-formedness predicate for file systems. As in your regular 
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
                       (ensures  (fun fs0 fs fs1 -> fs0 == fs /\ fs == fs1)) = 
  FileSystem?.read ()

let write (fs:wf_fs_tree) : FS unit 
                               (requires (fun _ -> True)) 
                               (ensures  (fun _ _ fs1 -> fs1 == fs)) = 
  FileSystem?.write fs


(* Task 3: Define both a pure function and a function in the `FS` effect that return all 
           the paths in a given (resp. current) file system. 

   Task 3 (Bonus): What additional properties could one prove about the `show` function?
                   Try extending the (currently trivial) specification of `show` with these
                   properties and prove that your implementation indeed satisfies them.

   Hint: The list of paths you get back is not any arbitrary list of paths. *)

let show_fs (fs:wf_fs_tree) : list path =
  admit ()

let show () : FS (list path)
                 (requires (fun fs0 -> True)) 
                 (ensures  (fun fs0 ps fs1 -> True)) =
  admit ()

(* Task 4: Define a function in the `FS` effect that creates a new directory in the file system. 

   Hint: As part of defining `create_dir`, you also need to prove that creating a well-formed 
         path in a well-formed tree results in a well-formed tree. *)

let create_dir (p:path) : FS unit 
                             (requires (fun fs0 -> True)) 
                             (ensures  (fun fs0 _ fs1 -> True)) = 
  admit ()

(* Task 5: Define a function in the `FS` effect that deletes a given path from the file system. 

   Hint: As part of defining `delete`, you also need to prove that deleting a well-formed path 
         from a well-formed tree results in a well-formed tree. *)

let delete (p:path) : FS unit
                         (requires (fun fs0 -> True))
                         (ensures  (fun fs0 _ fs1 -> True)) =
  admit ()

(* Task 6: Strengthen the specifications of `create_dir` and `delete` so that the test programs 
           in `FileSystemClient.fst` successfully typechecks. 
               
   Hint: Think about the resulting shape of the file system after creating a new path in it or 
         removing an already existing path. You can draw inspiration from the `deleteDeletes`
         and `createAndDelete` FSCheck properties you defined in your regular coursework. *)
