module FileSystemClient

(*

   Homework exercise.

   See `FileSystem.fst` for details.

*)

open FileSystem

open FStar.List.Tot

let test1 (p:path) : FS unit
                        (requires (fun fs0 -> fs0 == Node []))
                        (ensures  (fun fs0 _ fs1 -> fs0 == fs1)) =
  create_dir p;
  let _ = show () in
  delete p

let test2 (p:path) : FS (list path)
                        (requires (fun fs0 -> fs0 == Node []))
                        (ensures  (fun fs0 ps fs1 -> 
                                     count p ps == 1 /\
                                     fs0 == fs1)) =
  create_dir p;
  let ps = show () in
  delete p;
  ps

let test3 (p:path) : FS unit 
                        (requires (fun fs0 -> fs0 == Node []))
                        (ensures  (fun fs0 _ fs1 -> fs0 == fs1)) =
  create_dir p;
  delete p

let test4 (p1 p2 p3:path) : FS unit 
                               (requires (fun fs0 -> fs0 == Node []))
                               (ensures  (fun fs0 _ fs1 -> fs0 == fs1)) =
  create_dir p1;
  create_dir p2;
  delete p1;
  create_dir p3;
  delete p2;
  delete p3

let test5 (p1 p2:path) : FS unit
                        (requires (fun fs0 -> True))
                        (ensures  (fun _ _ fs1 -> 
                                    count p1 (show_fs fs1) == 1 /\ 
                                    count p2 (show_fs fs1) == 1)) =
  create_dir p1;
  create_dir p2

let test6 (p1 p2:path) : FS unit
                            (requires (fun fs0 -> True))
                            (ensures  (fun _ _ fs1 -> 
                                        count p1 (show_fs fs1) == 0 /\ 
                                        count p2 (show_fs fs1) == 0)) =
  delete p1;
  delete p2
