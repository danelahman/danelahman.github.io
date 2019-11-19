module FileSystemClient

(*

   Homework exercise.

   See `FileSystem.fst` for further details about this exercise.

   Below you can uncomment the `expect_failure` attributes in case
   you want to first make some of the the latter tests typecheck.

*)

open FileSystem

open FStar.List.Tot

//[@expect_failure]
let test1 (p:path) : FS unit 
                        (requires (fun fs0 -> fs0 == Node []))
                        (ensures  (fun fs0 _ fs1 -> fs0 == fs1)) =
  create_dir p;
  delete p

//[@expect_failure]
let test2 (p:path) : FS unit
                        (requires (fun fs0 -> fs0 == Node []))
                        (ensures  (fun fs0 _ fs1 -> fs0 == fs1)) =
  create_dir p;
  let _ = show () in
  delete p

//[@expect_failure]
let test2' (p:path) : FS unit
                         (requires (fun fs0 -> True))
                         (ensures  (fun fs0 _ fs1 -> in_fs p fs1)) =
  create_dir p

//[@expect_failure]
let test2'' (p:path) : FS unit
                         (requires (fun fs0 -> True))
                         (ensures  (fun fs0 _ fs1 -> ~(in_fs p fs1))) =
  delete p

//[@expect_failure]
let test3 (p:path) : FS (list path)
                        (requires (fun fs0 -> fs0 == Node []))
                        (ensures  (fun fs0 ps fs1 -> mem p ps /\ fs0 == fs1)) =
  create_dir p;
  let ps = show () in
  delete p;
  ps

//[@expect_failure]
let test4 (p1 p2 p3:path) : FS unit 
                               (requires (fun fs0 -> fs0 == Node []))
                               (ensures  (fun fs0 _ fs1 -> fs0 == fs1)) =
  create_dir p1;
  create_dir p2;
  delete p1;
  create_dir p3;
  delete p2;
  delete p3

//[@expect_failure]
let test5 (p1 p2:path) : FS unit
                        (requires (fun fs0 -> True))
                        (ensures  (fun _ _ fs1 -> in_fs p1 fs1 /\ in_fs p2 fs1)) =
  create_dir p1;
  create_dir p2

//[@expect_failure]
let test6 (p1 p2:path) : FS unit
                            (requires (fun fs0 -> True))
                            (ensures  (fun _ _ fs1 -> ~(in_fs p1 fs1) /\ ~(in_fs p2 fs1))) =
  delete p1;
  delete p2
