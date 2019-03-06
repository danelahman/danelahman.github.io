open Prims
let rec (ackermann : Prims.nat -> Prims.nat -> Prims.nat) =
  fun m  ->
    fun n  ->
      if m = (Prims.parse_int "0")
      then n + (Prims.parse_int "1")
      else
        if n = (Prims.parse_int "0")
        then ackermann (m - (Prims.parse_int "1")) (Prims.parse_int "1")
        else
          ackermann (m - (Prims.parse_int "1"))
            (ackermann m (n - (Prims.parse_int "1")))
  
let rec (swapped_ackermann : Prims.nat -> Prims.nat -> Prims.nat) =
  fun n  ->
    fun m  ->
      if m = (Prims.parse_int "0")
      then n + (Prims.parse_int "1")
      else
        if n = (Prims.parse_int "0")
        then
          swapped_ackermann (Prims.parse_int "1") (m - (Prims.parse_int "1"))
        else
          swapped_ackermann (swapped_ackermann (n - (Prims.parse_int "1")) m)
            (m - (Prims.parse_int "1"))
  
