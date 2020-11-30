open Prims
let rec (ackermann : Prims.nat -> Prims.nat -> Prims.nat) =
  fun m ->
    fun n ->
      if m = Prims.int_zero
      then n + Prims.int_one
      else
        if n = Prims.int_zero
        then ackermann (m - Prims.int_one) Prims.int_one
        else ackermann (m - Prims.int_one) (ackermann m (n - Prims.int_one))
let rec (swapped_ackermann : Prims.nat -> Prims.nat -> Prims.nat) =
  fun n ->
    fun m ->
      if m = Prims.int_zero
      then n + Prims.int_one
      else
        if n = Prims.int_zero
        then swapped_ackermann Prims.int_one (m - Prims.int_one)
        else
          swapped_ackermann (swapped_ackermann (n - Prims.int_one) m)
            (m - Prims.int_one)
let (swapped_ackermann_bad : Prims.nat -> Prims.nat -> Prims.nat) =
  fun n -> fun m -> failwith "Not yet implemented:swapped_ackermann_bad"
