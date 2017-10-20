{-# OPTIONS --without-K #-}

module HoareLogicFraming where

data Bool : Set where
  true  : Bool
  false : Bool

data _×_ (A B : Set) : Set where
  _,_ : (a : A) -> (b : B) -> A × B

_××_ : {A B C D : Set} -> (A -> C) -> (B -> D) -> A × B -> C × D
(f ×× g) (a , b) = (f a) , (g b)

postulate Value : Set
          Vars  : Set
          _=?=_   : Vars -> Vars -> Bool

data Command : Set where
  skip  : Command
  _:=_  : Vars -> Value -> Command
  _,_   : Command -> Command -> Command

Memory : Set
Memory = Vars -> Value

_[_/_] : Memory -> Value -> Vars -> Memory
(m [ v / x ]) y with x =?= y
(m [ v / x ]) y | true = v
(m [ v / x ]) y | false = m y

data ⟨_⟩_⟨_⟩ : (Memory -> Set) -> Command -> (Memory -> Set) -> Set₁ where
  skip : (P : Memory -> Set)
      -> ⟨ P ⟩ skip ⟨ P ⟩
  assignment : (P : Memory -> Set)
            -> (x : Vars)
            -> (v : Value)
            -> ⟨ (λ m -> P (m [ v / x ])) ⟩ x := v ⟨ P ⟩
  composition : (P Q R : Memory -> Set)
             -> (c1 c2 : Command)
             -> ⟨ P ⟩ c1 ⟨ Q ⟩
             -> ⟨ Q ⟩ c2 ⟨ R ⟩
             -> ⟨ P ⟩ c1 , c2 ⟨ R ⟩
  consequence : (P1 P2 Q1 Q2 : Memory -> Set)
             -> (c : Command)
             -> (imp1 : (m : Memory) -> P1 m -> P2 m)
             -> (imp2 : (m : Memory) -> Q2 m -> Q1 m)
             -> ⟨ P2 ⟩ c ⟨ Q2 ⟩
             -> ⟨ P1 ⟩ c ⟨ Q1 ⟩

framing-lemma : (P Q : Memory -> Set)
             -> (R : Set)
             -> (c : Command)
             -> ⟨ P ⟩ c ⟨ Q ⟩
             -> ⟨ (λ m -> P m × R) ⟩ c ⟨ (λ m -> Q m × R) ⟩
framing-lemma P .P R .skip (skip .P)
  = skip (λ m -> P m × R)
framing-lemma .(λ m -> Q (λ y -> (m [ v / x ]) y)) Q R .(x := v) (assignment .Q x v)
  = assignment (λ m -> Q m × R)
               x v
framing-lemma P Q R .(c1 , c2) (composition .P S .Q c1 c2 p q)
  = composition (λ m -> P m × R)
                (λ m -> S m × R)
                (λ m -> Q m × R)
                c1 c2
                (framing-lemma P S R c1 p)
                (framing-lemma S Q R c2 q)
framing-lemma P Q R c (consequence .P P2 .Q Q2 .c imp1 imp2 p)
  = consequence (λ m -> P m × R)
                (λ m -> P2 m × R)
                (λ m -> Q m × R)
                (λ m -> Q2 m × R)
                c
                (λ m -> (imp1 m) ×× (λ r -> r))
                (λ m -> (imp2 m) ×× (λ r -> r))
                (framing-lemma P2 Q2 R c p)
