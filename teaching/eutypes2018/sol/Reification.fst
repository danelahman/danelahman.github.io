module Reification

(**********************************************************
 *                                                        *
 * Dijkstra Monads for Free : Simple int-valued state     *
 *                                                        *
 **********************************************************)

let state = int

let st (a:Type) = state -> M (a * state)

let return_st (a:Type) (x:a) : st a 
  = fun s0 -> (x,s0)

let bind_st (a:Type) (b:Type) (f:st a) (g:a -> st b) : st b
  = fun s0 -> let (x,s) = f s0 in 
              g x s

let get () : st int 
  = fun s0 -> (s0,s0)

let put (x:int) : st unit 
  = fun s0 -> ((), x)

total reifiable reflectable new_effect {
  STATE : a:Type -> Effect
  with repr     = st
     ; bind     = bind_st
     ; return   = return_st
     ; get      = get
     ; put      = put
}

effect St (a:Type) = STATE a (fun _ p -> forall x s1 . p (x,s1))

(**********************************************************
 *                                                        *
 * Proof of stateful summing using reification            *
 *                                                        *
 **********************************************************)

open FStar.Mul

let sum_tot (n:nat) = ((n+1) * n) / 2

let rec sum_st (n:nat) : St unit
  = if n > 0 then (let x = STATE?.get () in 
                   STATE?.put (x + n);
                   sum_st (n - 1))

let lemma_sum_st (n:nat) : Lemma (let (_,s) = reify (sum_st n) 0 in s = sum_tot n)
  = ()

