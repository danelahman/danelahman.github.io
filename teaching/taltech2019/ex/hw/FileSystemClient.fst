module FileSystemClient

open FileSystem

open FStar.List.Tot

[@expect_failure]
let test1 (p:path) : FS unit
                        (requires (fun fs0 -> fs0 == None []))
                        (ensures  (fun fs0 _ fs1 -> fs0 == fs1)) =
  create_dir p;
  show
  delete p

[@expect_failure]
let test2 (p:path) : FS (list path)
                        (requires (fun fs0 -> fs0 == None []))
                        (ensures  (fun fs0 ps fs1 -> 
                                     fs0 == fs1 /\
                                     count p ps == 1)) =
  create_dir p;
  let ps = show () in
  delete p;
  ps

[@expect_failure]
let test3 (p:path) : FS unit 
                        (requires (fun fs0 -> fs0 == None []))
                        (ensures  (fun fs0 _ fs1 -> fs0 == fs1)) =
  create_dir p;
  delete p

[@expect_failure]
let test4 (p1 p2 p3:path) : FS unit 
                               (requires (fun fs0 -> fs0 == None []))
                               (ensures  (fun fs0 _ fs1 -> fs0 == fs1)) =
  create_dir p1;
  create_dir p2;
  delete p1;
  create_dir p3;
  delete p2;
  delete p3

[@expect_failure]
let test5 (p1 p2:path) : FS unit
                        (requires (fun fs0 -> True))
                        (ensures  (fun _ _ fs1 -> count p1 (show_fs fs1) == 1)) =
  create_dir p1;
  create_dir p2
