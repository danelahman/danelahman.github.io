{-# OPTIONS --without-K #-}

module HoareLogicFraming where

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

postulate Values : Set
          Vars   : Set
          _=?=_  : Vars → Vars → Bool

mutual
  data Prop : Set where
    ⊤   : Prop
    ⊥   : Prop
    _∧_ : Prop → Prop → Prop
    _∨_ : Prop → Prop → Prop
    _⇒_ : Prop → Prop → Prop
    ¬_  : Prop → Prop

  ⟦_⟧ : Prop -> Set
  ⟦ ⊤ ⟧ = One
  ⟦ ⊥ ⟧ = Zero
  ⟦ P ∧ Q ⟧ = ⟦ P ⟧ × ⟦ Q ⟧
  ⟦ P ∨ Q ⟧ = ⟦ P ⟧ + ⟦ Q ⟧
  ⟦ P ⇒ Q ⟧ = ⟦ P ⟧ → ⟦ Q ⟧
  ⟦ ¬ P ⟧ = ⟦ P ⟧ → Zero

Memory : Set
Memory = Vars → Values

_[_/_] : Memory → Values → Vars → Memory
(m [ v / x ]) y with x =?= y
(m [ v / x ]) y | true = v
(m [ v / x ]) y | false = m y

data Command : Set where
  skip  : Command
  _:=_  : Vars → Values → Command
  _,_   : Command → Command → Command
  if_then_else_ : (Memory → Prop) → Command → Command → Command

data ⟨_⟩_⟨_⟩ : (Memory → Set) → Command → (Memory → Set) → Set₁ where
  skip : (P : Memory → Set)
       → ⟨ P ⟩ skip ⟨ P ⟩
  assignment : (P : Memory → Set)
             → (x : Vars)
             → (v : Values)
             → ⟨ (λ m → P (m [ v / x ])) ⟩ x := v ⟨ P ⟩
  composition : (P Q R : Memory → Set)
              → (c1 c2 : Command)
              → ⟨ P ⟩ c1 ⟨ Q ⟩
              → ⟨ Q ⟩ c2 ⟨ R ⟩
              → ⟨ P ⟩ c1 , c2 ⟨ R ⟩
  conditional : (P Q : Memory → Set)
              → (B : Memory → Prop)
              → (c1 c2 : Command)
              → ⟨ (λ m → ⟦ B m ⟧ × P m) ⟩ c1 ⟨ Q ⟩
              → ⟨ (λ m → ⟦ (¬ (B m)) ⟧ × P m ) ⟩ c2 ⟨ Q ⟩
              → ⟨ P ⟩ if B then c1 else c2 ⟨ Q ⟩
  consequence : (P1 P2 Q1 Q2 : Memory → Set)
              → (c : Command)
              → (imp1 : (m : Memory) → P1 m → P2 m)
              → (imp2 : (m : Memory) → Q2 m → Q1 m)
              → ⟨ P2 ⟩ c ⟨ Q2 ⟩
              → ⟨ P1 ⟩ c ⟨ Q1 ⟩

framing-lemma : (P Q : Memory → Set)
              → (R : Set)
              → (c : Command)
              → ⟨ P ⟩ c ⟨ Q ⟩
              → ⟨ (λ m → P m × R) ⟩ c ⟨ (λ m → Q m × R) ⟩
framing-lemma P .P R .skip (skip .P)
  = skip (λ m → P m × R)
framing-lemma .(λ m → Q (λ y → (m [ v / x ]) y)) Q R .(x := v) (assignment .Q x v)
  = assignment (λ m → Q m × R)
               x v
framing-lemma P Q R .(c1 , c2) (composition .P S .Q c1 c2 p q)
  = composition (λ z → P z × R)
                (λ z → S z × R)
                (λ z → Q z × R)
                c1 c2
                (framing-lemma P S R c1 p)
                (framing-lemma S Q R c2 q)
framing-lemma P Q R .(if B then c1 else c2) (conditional .P .Q B c1 c2 p q)
  = conditional (λ m → P m × R)
                (λ m → Q m × R)
                B
                c1 c2
                (consequence (λ m → ⟦ B m ⟧ × (P m × R))
                             (λ m → (⟦ B m ⟧ × P m) × R)
                             (λ m → Q m × R)
                             (λ m → Q m × R)
                             c1
                             (λ m → ×-assoc2)
                             (λ m p → p)
                             (framing-lemma (λ m → ⟦ B m ⟧ × P m) Q R c1 p))
                (consequence (λ m → ⟦ ¬ (B m) ⟧ × (P m × R))
                             (λ m → (⟦ ¬ (B m) ⟧ × P m) × R)
                             (λ m → Q m × R)
                             (λ m → Q m × R)
                             c2
                             (λ m → ×-assoc2)
                             (λ m q → q)
                             (framing-lemma (λ m → ⟦ ¬ (B m) ⟧ × P m) Q R c2 q))
framing-lemma P Q R c (consequence .P P2 .Q Q2 .c imp1 imp2 p)
  = consequence (λ m → P m × R)
                (λ m → P2 m × R)
                (λ m → Q m × R)
                (λ m → Q2 m × R)
                c
                (λ m → (imp1 m) ×× (λ r → r))
                (λ m → (imp2 m) ×× (λ r → r))
                (framing-lemma P2 Q2 R c p)


{-framing-lemma : (P Q : Memory → Set)
              → (R : Set)
              → (c : Command)
              → ⟨ P ⟩ c ⟨ Q ⟩
              → ⟨ (λ m → P m × R) ⟩ c ⟨ (λ m → Q m × R) ⟩
framing-lemma P .P R .skip (skip .P)
  = skip (λ m → P m × R)
framing-lemma .(λ m → Q (λ y → (m [ v / x ]) y)) Q R .(x := v) (assignment .Q x v)
  = assignment (λ m → Q m × R)
               x v
framing-lemma P Q R .(c1 , c2) (composition .P S .Q c1 c2 p q)
  = composition (λ m → P m × R)
                (λ m → S m × R)
                (λ m → Q m × R)
                c1 c2
                (framing-lemma P S R c1 p)
                (framing-lemma S Q R c2 q)
framing-lemma P Q R c (consequence .P P2 .Q Q2 .c imp1 imp2 p)
  = consequence (λ m → P m × R)
                (λ m → P2 m × R)
                (λ m → Q m × R)
                (λ m → Q2 m × R)
                c
                (λ m → (imp1 m) ×× (λ r → r))
                (λ m → (imp2 m) ×× (λ r → r))
                (framing-lemma P2 Q2 R c p)-}
