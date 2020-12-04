module FileSystem

(* 

  Homework exercise.

  In this exercise you are asked to implement an FStar-version of the 
  small file system from your coursework no. 7. This exercise differs 
  from your regular coursework in that we will not use randomised 
  testing to check the correctness of your implementation, but instead 
  you are asked to equip the `create` and `delete` functions with strong
  specifications, and prove that your implementations satisfy them.

  The exercise is divided into 7 tasks---see below for further details. 
  The tasks are somewhat independent. For instance, you can either first
  implement the file system operations (Tasks 4-6) and then strengthen 
  their specifications (Task 7); or you can first try to come up with 
  suitably strong specifications for them to verify `FileSystemClient.fst`
  (Task 7), and only afterwards try to come up with the actual 
  implementations that would satisfy these stronger specifications.

  When solving the tasks below, do not be afraid of defining additional 
  auxiliary (pure) recursive functions, state and prove lemmas about 
  these functions, and then use them in the various specifications.

*)

open FStar.List.Tot // FStar's lists library which could be useful below
open FStar.Classical // FStar's classical logic library which could also be useful below


(*

   The raw file system and raw paths in it are defined exactly as in your 
   regular coursework: raw paths are lists of strings, and the type of 
   raw file systems is a recursively defined tree-like record datatype.
   
*)

type path = list string

type fstree = { name:string ;
                children:list fstree }

let mk_fstree (name:string) (children:list fstree) =
  { name = name; children = children }



(* 

  Task 1: Define the type `wf_path` of well-formed paths as raw paths that:

          - do not contain nodes with empty names; and 

          - are nonempty (this is a stronger condition than required by the
            `pathWf` predicate in your regular coursework, but it will make 
            defining the file system operations below more convenient). 
                    
          In other words, replace the `admit` in `path_wf` with a (bool-valued) 
          predicate on the path `p` that ensures this kind of well-formedness.
          
*)

let rec path_wf (p:path) : bool = 
  admit ()
  
type wf_path = p:path{path_wf p}


(*

  Sanity checking that you got the well-formedness of raw paths correct. 
  
*)

let check_wf_path () : Lemma (path_wf ("home" :: "username" :: [])) = 
  ()

let check_not_wf_path () : Lemma (~(path_wf ("home" :: "" :: "username" :: []))) = 
  ()



(* 

  Task 2: Define the type `wf_fstree` of well-formed file systems as a refinement 
          of raw file systems. That is, replace the `admit` in `fstree_wf` with a 
          predicate which ensures that in the given file system `fs`:
          
          - the path to any directory in the file system is well-formed; and
            
          - the file system is deterministic (for any given path, there is at most 
            one directory in the file system with that path.
            
*)

let rec fstree_wf (fs:fstree) : bool = 
  admit ()

let wf_fstree = fs:fstree{fstree_wf fs}


(* 

  Sanity checking that you got the well-formedness of raw file systems correct. 
  
*)

let check_wf_fs () 
  : Lemma (fstree_wf (
      mk_fstree "/"
        [
        mk_fstree "home"
        [ 
          mk_fstree "username1" 
          [
            mk_fstree "documents" [];
            mk_fstree "downloads" [];            
          ];
          mk_fstree "username2" 
          [
            mk_fstree "documents" []
          ]
        ]
        ])) = 
  ()

let check_not_wf_fs_path () 
  : Lemma (not (fstree_wf (
      mk_fstree "/"
        [
        mk_fstree "home"
        [ 
          mk_fstree "username1" 
          [
            mk_fstree "documents" [];
            mk_fstree "downloads" [];            
          ];
          mk_fstree "" 
          [
            mk_fstree "documents" []
          ]
        ]
        ]))) =
  ()

let check_not_wf_fs_nondet () 
  : Lemma (not (fstree_wf (
      mk_fstree "/"
        [
        mk_fstree "home"
        [ 
          mk_fstree "username" 
          [
            mk_fstree "documents" [];
            mk_fstree "downloads" [];            
          ];
          mk_fstree "username" 
          [
            mk_fstree "documents" []
          ]
        ]
        ]))) =
  ()



(*

  Task 3: Define a predicate on (raw) file systems  that holds if a  
          given well-formed path exists in a given (raw) file system.

          For convenience, we use the convention here that the path `p` 
          is given relative to the root directory (but **does not** 
          contain the root). So, if the root of a file system `fs` is "/", 
          then `in_fstree ["home"; "username"] fs` holds if the file
          system `fs` includes the path `["/"; "home"; "username"]`.
          
*)

let rec in_fstree (p:wf_path) (fs:fstree) : bool = 
  admit ()



(* 

  Sanity checking that you got the path inclusion predicate correct. 
  
*)

let check_in_fstree1 ()
  : Lemma (["home"; "username1"; "downloads"]
           `in_fstree`
           mk_fstree "/"
             [
             mk_fstree "home"
             [
               mk_fstree "username1" 
               [
                 mk_fstree "documents" [];
                 mk_fstree "downloads" [];            
               ];
               mk_fstree "username2" 
               [
                 mk_fstree "documents" []
               ]
             ]
           ]) =
  ()

let check_in_fstree2 ()
  : Lemma (["home"; "username2"] 
           `in_fstree`
           mk_fstree "/"
             [
             mk_fstree "home"
             [
               mk_fstree "username1" 
               [
                 mk_fstree "documents" [];
                 mk_fstree "downloads" [];            
               ];
               mk_fstree "username2" 
               [
                 mk_fstree "documents" []
               ]
             ]
           ]) =
  ()

let check_not_in_fstree ()
  : Lemma (not (["home"; "username3"; "downloads"]
                `in_fstree`
                mk_fstree "/"
                  [
                  mk_fstree "home"
                  [
                    mk_fstree "username1" 
                    [
                      mk_fstree "documents" [];
                      mk_fstree "downloads" [];            
                    ];
                    mk_fstree "username2" 
                    [
                      mk_fstree "documents" []
                    ]
                  ]
                ])) =
  ()



(*

  Task 4: Prove that if a path is included in a given file system,
          then any prefix of this path is also in that file system.

          These lemmas and the SMT patterns attached to them will
          help us to automatically deduce that if `["a"; "b"; "c"]`
          is a well-formed path, then so are `["a"]` and `["a"; "b"]`, 
          and similarly for the containment of prefixes in file systems.

*)

let rec lemma_path_wf_append (p q:path)
  : Lemma (requires (path_wf p /\ path_wf q))
          (ensures  (path_wf (append p q)))
          [SMTPat (path_wf (append p q))] =
  admit ()

let rec lemma_in_fstree_append (p q:wf_path) (fs:fstree)
  : Lemma (requires (append p q `in_fstree` fs))
          (ensures  (p `in_fstree` fs))
          [SMTPat (append p q `in_fstree` fs); 
           SMTPat (p `in_fstree` fs)] = 
  admit ()



(*

  A (monadic) effect that characterises programs that use a file system. 
  
*)

let fs_st (a:Type) = fstree -> M (a * fstree)

let return_fs_st (a:Type) (x:a) : fs_st a 
  = fun fs0 -> (x,fs0)

let bind_fs_st (a:Type) (b:Type) (f:fs_st a) (g:a -> fs_st b) : fs_st b
  = fun fs0 -> let (x,fs1) = f fs0 in 
              g x fs1

let read_st () : fs_st fstree 
  = fun fs0 -> (fs0,fs0)

let write_st (fs:fstree) : fs_st unit 
  = fun _ -> ((), fs)

total new_effect {
  FileSystem : a:Type -> Effect
  with repr     = fs_st
     ; bind     = bind_fs_st
     ; return   = return_fs_st
     ; read     = read_st
     ; write    = write_st
}


(* 

  A pre- and postcondition variant of the `FileSystem` effect, which additionally 
  assumes that the initial file system (`fs0`) is well-formed and additionally 
  requires one to prove that the final file system (`fs1`) remains well-formed. 
   
*)

effect FS (a:Type) 
          (pre:wf_fstree -> Type0) 
          (post:wf_fstree -> a -> wf_fstree -> Type0) = 
  FileSystem a (fun fs0 p -> 
                 fstree_wf fs0 /\ 
                 pre fs0 /\ 
                 (forall x fs1 . (post fs0 x fs1 /\ fstree_wf fs1) ==> p (x,fs1)))


(* 

  Effectful actions to read and update the file system in your code below. 
  
*)

let read (_:unit) : FS wf_fstree
                       (requires (fun _ -> True)) 
                       (ensures  (fun fs0 fs fs1 -> fs0 == fs /\ fs == fs1)) = 
  FileSystem?.read ()

let write (fs:wf_fstree) : FS unit 
                              (requires (fun _ -> True)) 
                              (ensures  (fun _ _ fs1 -> fs1 == fs)) = 
  FileSystem?.write fs
  


(* 

  Task 5: Define a function in the `FS` effect that creates a new directory in the 
          file system. If the directory exists, then keep the file system as is.

          For convenience, we use the convention here that the path `p` is given
          relative to the root directory (but **does not** contain the root). So, if
          the root of a file system `fs` is "/", then `create ["home"; "username"] fs`
          would create a new directory at path `["/"; "home"; "username"]` in `fs`.

  Hint: As part of defining `create`, you need to prove that creating a well-formed
        path in a well-formed file system results in a well-formed file system. 
        
*)

let create (p:wf_path) : FS unit 
                            (requires (fun fs0 -> True)) 
                            (ensures  (fun fs0 _ fs1 -> True)) = 
  admit ()



(*

  Task 6: Define a function in the `FS` effect that deletes a given path from the file system. 

          For convenience, we again use the convention here that the path `p` is given
          relative to the root directory (but **does not** contain the root). So, if
          the root of a file system `fs` is "/", then `delete ["home"; "username"] `fs``
          would delete the directory at path `["/"; "home"; "username"]` in `fs`.

  Hint: As part of defining `delete`, you also need to prove that deleting a well-formed path 
        from a well-formed tree results in a well-formed tree. 

*)

let delete (p:wf_path) : FS unit
                            (requires (fun fs0 -> True))
                            (ensures  (fun fs0 _ fs1 -> True)) =
  admit ()



(* 

  Task 7: Strengthen the (currently trivial) specifications of `create` and `delete`
          so that the test code in `FileSystemClient.fst` successfully typechecks. 
               
  Hint 1: Think about the resulting shape of the file system after creating a new path
          in it or removing an already existing path. You can draw inspiration from the 
          `deleteDeletes` and `createAndDelete` FSCheck properties you defined in your 
          regular coursework. 

  Hint 2: Do not be afraid of defining auxiliary pure functions (using the default `Tot` 
          effect) which you can then use as part of the specifications. Most probably
          you will also need to state and prove some lemmas about these functions (using 
          the `Lemma` effect), e.g., so as to relate the spec of `create` to the spec of 
          `delete` if one follows the other in user code (as in FileSystemClient.fst).

*)
