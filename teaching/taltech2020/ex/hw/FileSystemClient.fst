module FileSystemClient

(*

   Homework exercise.

   See `FileSystem.fst` for further details about this exercise.

   Below you can uncomment the `expect_failure` attributes in case
   you want to first make some of the the latter tests typecheck.

*)

open FStar.List.Tot

open FileSystem

//[@(expect_failure)]
let test0 (p:wf_path) : FS unit
                           (requires (fun fs0 -> (["home"] @ ["username"]) `in_fstree` fs0))
                           (ensures  (fun _ _ fs1 -> ["home"] `in_fstree` fs1)) =
  ()

//[@(expect_failure)]
let test1 (p:wf_path) : FS unit
                           (requires (fun fs0 -> True))
                           (ensures  (fun _ _ fs1 -> p `in_fstree` fs1)) =
  create p

//[@(expect_failure)]
let test2 (p:wf_path) : FS unit
                           (requires (fun fs0 -> True))
                           (ensures  (fun _ _ fs1 -> not (p `in_fstree` fs1))) =
  delete p

//[@(expect_failure)]
let test3 (p q:wf_path) : FS unit
                             (requires (fun fs0 -> p `in_fstree` fs0))
                             (ensures  (fun _ _ fs1 -> p `in_fstree` fs1 /\ q `in_fstree` fs1)) =
  create q

//[@(expect_failure)]
let test4 (p q r:wf_path) : FS unit
                             (requires (fun fs0 -> p `in_fstree` fs0))
                             (ensures  (fun _ _ fs1 -> p `in_fstree` fs1 /\ q `in_fstree` fs1 /\ r `in_fstree` fs1)) =
  create q;
  create r

//[@(expect_failure)]
let test5 () : FS unit
                  (requires (fun fs0 -> (["home"] @ ["username1"]) `in_fstree` fs0))
                  (ensures  (fun _ _ fs1 -> (["home"] @ ["username1"]) `in_fstree` fs1)) =
  delete ["home"; "username2"]

//[@(expect_failure)]
let test6 () : FS unit
                  (requires (fun fs0 -> (["home"] @ ["username"] @ ["documents"]) `in_fstree` fs0 /\
                                     (["home"] @ ["username"] @ ["downloads"]) `in_fstree` fs0))
                  (ensures  (fun _ _ fs1 -> not ((["home"] @ ["username"] @ ["documents"]) `in_fstree` fs1) /\
                                         not ((["home"] @ ["username"] @ ["downloads"]) `in_fstree` fs1))) =
  delete (["home"] @ ["username"])


//[@(expect_failure)]
let test7 () : FS unit
                  (requires (fun fs0 -> (["home"] @ ["username1"]) `in_fstree` fs0 /\
                                     (["home"] @ ["username2"] @ ["documents"]) `in_fstree` fs0 /\
                                     (["home"] @ ["username3"]) `in_fstree` fs0))
                  (ensures  (fun _ _ fs1 -> (["home"] @ ["username2"] @ ["documents"]) `in_fstree` fs1)) =
  delete (["home"] @ ["username1"]);
  delete (["home"] @ ["username3"])

//[@(expect_failure)]
let test8 (p:wf_path) : FS unit
                           (requires (fun fs0 -> True))
                           (ensures  (fun _ _ fs1 -> not ((["home"] @ ["username"]) `in_fstree` fs1))) =
  create (["home"] @ ["username"]);
  delete (["home"] @ ["username"])

//[@(expect_failure)]
let test9 (p:wf_path) : FS unit
                           (requires (fun fs0 -> True))
                           (ensures  (fun _ _ fs1 -> (["home"] @ ["username2"] @ ["downloads"]) `in_fstree` fs1 /\
                                                  not ((["home"] @ ["username1"] @ ["documents"]) `in_fstree` fs1) /\
                                                  not ((["home"] @ ["username1"]) `in_fstree` fs1) /\
                                                  (["home"] @ ["username3"]) `in_fstree` fs1)) =
  create (["home"] @ ["username1"]);
  create (["home"] @ ["username2"]);
  create (["home"] @ ["username1"] @ ["documents"]);
  create (["home"] @ ["username2"] @ ["downloads"]);
  delete (["home"] @ ["username1"]);
  create (["home"] @ ["username3"])
