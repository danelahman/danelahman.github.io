module FibonacciReify

(**********************************************************
 *                                                        *
 * Dijkstra Monads for Free : Simple int-valued state     *
 *                                                        *
 **********************************************************)

let state = int * int

let st (a:Type) = state -> M (a * state)

let return_st (a:Type) (x:a) : st a 
  = fun s0 -> (x,s0)

let bind_st (a:Type) (b:Type) (f:st a) (g:a -> st b) : st b
  = fun s0 -> let (x,s) = f s0 in 
              g x s

let get_left () : st int 
  = fun s0 -> (fst s0,s0)

let get_right () : st int 
  = fun s0 -> (snd s0,s0)

let put_left (x:int) : st unit 
  = fun s0 -> ((), (x,snd s0))

let put_right (x:int) : st unit 
  = fun s0 -> ((), (fst s0,x))

total reifiable reflectable new_effect {
  STATE : a:Type -> Effect
  with repr      = st
     ; bind      = bind_st
     ; return    = return_st
     ; get_left  = get_left
     ; get_right = get_right
     ; put_left  = put_left
     ; put_right = put_right
}

#reset-options

effect St (a:Type) = STATE a (fun _ p -> forall x s1 . p (x,s1))

(**********************************************************
 *                                                        *
 * Proof of stateful fibonacci using reification          *
 *                                                        *
 **********************************************************)

let rec fibonacci_tot (n:nat) : Tot nat 
  = if n <= 1 then 1 else fibonacci_tot (n - 1) + fibonacci_tot (n - 2)

let rec fibonacci (i:pos) (n:nat{n >= i}) : St unit (decreases (n - i)) = 
  if i < n then (let temp = STATE?.get_right () in
                 STATE?.put_right (STATE?.get_left () + STATE?.get_right ()); 
                 STATE?.put_left temp;
                 fibonacci (i+1) n)

let rec lemma_fibonacci (i:pos) (n:nat{n >= i})
  : Lemma (requires True)
          (ensures (let (_,(s,s')) = reify (fibonacci i n) (1,1) in 
                    s' = fibonacci_tot (n - i)))
          (decreases (n - i))
= if i = n then ()
           else admit ()//; lemma_fibonacci (i+1) n
