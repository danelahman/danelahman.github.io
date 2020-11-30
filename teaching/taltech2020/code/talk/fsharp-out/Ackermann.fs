#light "off"

module Ackermann

open Prims
open FStar_Pervasives

let rec ackermann : Prims.nat -> Prims.nat -> Prims.nat = 
    (fun (m : Prims.nat) (n : Prims.nat) -> 
    (match ((Prims.op_Equality m (Prims.parse_int "0"))) with
     | true -> ((n + (Prims.parse_int "1")))
     | uu___ -> 
         ((match ((Prims.op_Equality n (Prims.parse_int "0"))) with
           | true -> 
               ((ackermann (m - (Prims.parse_int "1")) (Prims.parse_int "1")))
           | uu___1 -> 
               ((ackermann (m - (Prims.parse_int "1")) 
                     (ackermann m (n - (Prims.parse_int "1")))))))))

let rec swapped_ackermann : Prims.nat -> Prims.nat -> Prims.nat = 
    (fun (n : Prims.nat) (m : Prims.nat) -> 
    (match ((Prims.op_Equality m (Prims.parse_int "0"))) with
     | true -> ((n + (Prims.parse_int "1")))
     | uu___ -> 
         ((match ((Prims.op_Equality n (Prims.parse_int "0"))) with
           | true -> 
               ((swapped_ackermann (Prims.parse_int "1") 
                     (m - (Prims.parse_int "1"))))
           | uu___1 -> 
               ((swapped_ackermann 
                     (swapped_ackermann (n - (Prims.parse_int "1")) m) 
                     (m - (Prims.parse_int "1"))))))))

let swapped_ackermann_bad : Prims.nat -> Prims.nat -> Prims.nat = 
    (fun (n : Prims.nat) (m : Prims.nat) -> 
    (failwith "Not yet implemented:swapped_ackermann_bad"))
