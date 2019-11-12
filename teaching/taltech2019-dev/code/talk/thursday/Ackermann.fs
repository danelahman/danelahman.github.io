#light "off"
module Ackermann
open Prims
open FStar.Pervasives

let rec ackermann : Prims.nat  ->  Prims.nat  ->  Prims.nat = (fun ( m  :  Prims.nat ) ( n  :  Prims.nat ) -> (match ((Prims.op_Equality m (Prims.parse_int "0"))) with
| true -> begin
(n + (Prims.parse_int "1"))
end
| uu____41 -> begin
(match ((Prims.op_Equality n (Prims.parse_int "0"))) with
| true -> begin
(ackermann (m - (Prims.parse_int "1")) (Prims.parse_int "1"))
end
| uu____58 -> begin
(ackermann (m - (Prims.parse_int "1")) (ackermann m (n - (Prims.parse_int "1"))))
end)
end))


let rec swapped_ackermann : Prims.nat  ->  Prims.nat  ->  Prims.nat = (fun ( n  :  Prims.nat ) ( m  :  Prims.nat ) -> (match ((Prims.op_Equality m (Prims.parse_int "0"))) with
| true -> begin
(n + (Prims.parse_int "1"))
end
| uu____121 -> begin
(match ((Prims.op_Equality n (Prims.parse_int "0"))) with
| true -> begin
(swapped_ackermann (Prims.parse_int "1") (m - (Prims.parse_int "1")))
end
| uu____138 -> begin
(swapped_ackermann (swapped_ackermann (n - (Prims.parse_int "1")) m) (m - (Prims.parse_int "1")))
end)
end))







