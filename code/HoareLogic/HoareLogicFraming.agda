{-# OPTIONS --without-K #-}

module HoareLogicFraming where

-- A simple prelude of finite coproducts and finite products

data Zero : Set where

data One : Set where
  ⋆ : One

data Bool : Set where
  true  : Bool
  false : Bool

data _+_ (A B : Set) : Set where
  inl : A → A + B
  inr : B → A + B

data _×_ (A B : Set) : Set where
  _,_ : (a : A) → (b : B) → A × B

×-assoc1 : {A B C : Set} → (A × B) × C → A × (B × C)
×-assoc1 ((a , b) , c) = a , (b , c)

×-assoc2 : {A B C : Set} → A × (B × C) → (A × B) × C
×-assoc2 (a , (b , c)) = (a , b) , c

_××_ : {A B C D : Set} → (A → C) → (B → D) → A × B → C × D
(f ×× g) (a , b) = (f a) , (g b)


-- Assumed types of values and variables with boolean-decidable equality

postulate Values : Set
          Vars   : Set
          _=?=_  : Vars → Vars → Bool


-- A universe of propositions for conditionals

mutual
  data Prop : Set where
    ⊤   : Prop
    ⊥   : Prop
    _∧_ : Prop → Prop → Prop
    _∨_ : Prop → Prop → Prop
    _⇒_ : Prop → Prop → Prop
    ¬_  : Prop → Prop

  ⟦_⟧ : Prop → Set
  ⟦ ⊤ ⟧ = One
  ⟦ ⊥ ⟧ = Zero
  ⟦ P ∧ Q ⟧ = ⟦ P ⟧ × ⟦ Q ⟧
  ⟦ P ∨ Q ⟧ = ⟦ P ⟧ + ⟦ Q ⟧
  ⟦ P ⇒ Q ⟧ = ⟦ P ⟧ → ⟦ Q ⟧
  ⟦ ¬ P ⟧ = ⟦ P ⟧ → Zero


-- Memories and memory updates

Memory : Set
Memory = Vars → Values

_[_/_] : Memory → Values → Vars → Memory
(m [ v / x ]) y with x =?= y
(m [ v / x ]) y | true = v
(m [ v / x ]) y | false = m y


-- Commands

data Command : Set where
  skip  : Command
  _:=_  : Vars → Values → Command
  _,_   : Command → Command → Command
  if_then_else_ : (Memory → Prop) → Command → Command → Command


-- Hoare triples

data ⟨_⟩_⟨_⟩ : (Memory → Set) → Command → (Memory → Set) → Set₁ where
  skip : {P : Memory → Set}
       → ⟨ P ⟩ skip ⟨ P ⟩
  assignment : {P : Memory → Set}
             → (x : Vars)
             → (v : Values)
             → ⟨ (λ m → P (m [ v / x ])) ⟩ x := v ⟨ P ⟩
  composition : {P : Memory → Set}
              → (Q : Memory → Set)
              → {R : Memory → Set}
              → {c1 c2 : Command}
              → ⟨ P ⟩ c1 ⟨ Q ⟩
              → ⟨ Q ⟩ c2 ⟨ R ⟩
              → ⟨ P ⟩ c1 , c2 ⟨ R ⟩
  conditional : {P Q : Memory → Set}
              → {B : Memory → Prop}
              → {c1 c2 : Command}
              → ⟨ (λ m → ⟦ B m ⟧ × P m) ⟩ c1 ⟨ Q ⟩
              → ⟨ (λ m → ⟦ (¬ (B m)) ⟧ × P m ) ⟩ c2 ⟨ Q ⟩
              → ⟨ P ⟩ if B then c1 else c2 ⟨ Q ⟩
  consequence : {P1 P2 Q1 Q2 : Memory → Set}
              → {c : Command}
              → (imp1 : (m : Memory) → P1 m → P2 m)
              → (imp2 : (m : Memory) → Q2 m → Q1 m)
              → ⟨ P2 ⟩ c ⟨ Q2 ⟩
              → ⟨ P1 ⟩ c ⟨ Q1 ⟩


-- Framing of state-independent predicates

framing-lemma : (P Q : Memory → Set)
              → (R : Memory → Set)
              → (i : {m1 m2 : Memory} → R m1 → R m2) -- state independence
              → (c : Command)
              → ⟨ P ⟩ c ⟨ Q ⟩
              → ⟨ (λ m → P m × R m) ⟩ c ⟨ (λ m → Q m × R m) ⟩
framing-lemma P .P R i .skip skip
  = skip
framing-lemma .(λ m → Q (λ y → (m [ v / x ]) y)) Q R i .(x := v) (assignment x v)
  = consequence (λ m → λ { (q , r) → q , i r})
                (λ m qr → qr)
                (assignment x v)
framing-lemma P Q R i (c1 , c2) (composition S p q)
  = composition (λ m → S m × R m)
                (framing-lemma P S R i c1 p)
                (framing-lemma S Q R i c2 q)
framing-lemma P Q R i (if B then c1 else c2) (conditional p q)
  = conditional (consequence (λ m → ×-assoc2)
                             (λ m qr → qr)
                             (framing-lemma (λ m → ⟦ B m ⟧ × P m) Q R i c1 p))
                (consequence (λ m → ×-assoc2)
                             (λ m qr → qr)
                             (framing-lemma (λ m → ⟦ ¬ (B m) ⟧ × P m) Q R i c2 q))
framing-lemma P Q R i c (consequence {.P} {P2} {.Q} {Q2} imp1 imp2 p)
  = consequence (λ m → (imp1 m) ×× (λ r → r))
                (λ m → (imp2 m) ×× (λ r → r))
                (framing-lemma P2 Q2 R i c p)

