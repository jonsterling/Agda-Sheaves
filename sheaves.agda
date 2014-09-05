{-# OPTIONS --type-in-type #-}

record ⊤ : Set where
  constructor tt

data ⊥ : Set where

data _==_ {A : Set} (x : A) : A → Set where
  refl : x == x

module _ (A : Set) (B : A → Set) where
  record Σ : Set where
    constructor _,_
    field
      π₁ : A
      π₂ : B π₁
  open Σ public
  syntax Σ A (λ x → B) = Σ[ x ∶ A ] B

isContr : Set → Set
isContr A = Σ[ x ∶ A ] (∀ y → x == y)

Σ! : (A : Set) (B : A → Set) → Set
Σ! A B = isContr (Σ A B)

syntax Σ! A (λ x → B) = Σ![ x ∶ A ] B

_×_ : (A B : Set) → Set
A × B = Σ A λ _ → B

P : Set → Set
P A = A → Set

module _ {A : Set} where
  empty : P A
  empty = λ x → ⊥

  full : P A
  full = λ x → ⊤

  _∩_ : P A → P A → P A
  U ∩ V = λ x → (U x) × (V x)

  _⊆_ : P A → P A → Set
  U ⊆ V = ∀ x → U x → V x

  ⋃[_] : P (P A) → P A
  ⋃[_] S = λ x → Σ[ U ∶ P A ] S U × U x

record Topology (X : Set) : Set where
  field
    O : P (P X)

    empty-open : O empty
    full-open : O full
    inter-open : ∀ {U V} → O U → O V → O (U ∩ V)
    union-open : ∀ {S} → S ⊆ O → O ⋃[ S ]

record Equivalence {A : Set} (R : A → A → Set) : Set where
  field
    reflexivity : {x : A} → R x x
    !_ : {x y : A} → R x y → R y x
    _∙_ : {x y z : A} → R y z → R x y → R x z
  infixr 9 _∙_

instance
  ==-equiv : ∀ {A} → Equivalence (_==_ {A})
  ==-equiv = record { reflexivity = refl ; !_ = λ { {_} {._} refl → refl }; _∙_ = λ { {_} {._} {_} refl q → q } }

record Category : Set where
  field
    Ob : Set
    Hom : Ob → Ob → Set

    _~_ : ∀ {A B} → Hom A B → Hom A B → Set
    ~-equiv : ∀ {A B} → Equivalence (_~_ {A} {B})

    id : ∀ {A} → Hom A A
    _∘_ : ∀ {A B C} → Hom B C → Hom A B → Hom A C

    left-id : ∀ {A B} {f : Hom A B} → (id ∘ f) ~ f
    right-id : ∀ {A B} {f : Hom A B} → (f ∘ id) ~ f

    assoc : ∀ {A B C D} {f : Hom A B} {g : Hom B C} {h : Hom C D} → ((h ∘ g) ∘ f) ~ (h ∘ (g ∘ f))

  instance
    ~-equiv-instance = ~-equiv

    opposite : Category
    opposite =
      let open Equivalence {{...}} in
      record
      { Ob = Ob
      ; Hom = λ A B → Hom B A
      ; _~_ = _~_
      ; ~-equiv = ~-equiv
      ; id = id
      ; _∘_ = λ f g → g ∘ f
      ; left-id = λ {A} {B} → right-id
      ; right-id = λ {A} {B} → left-id
      ; assoc = λ {A} {B} {C} {D} {f} {g} {h} → ! assoc
      }


record Functor (C D : Category) : Set where
  module C = Category C
  module D = Category D

  field
    apply : C.Ob → D.Ob
    map : ∀ {A B} → C.Hom A B → D.Hom (apply A) (apply B)

    id-law : ∀ {A} → map (C.id {A}) D.~ D.id
    comp-law : ∀ {A B C} (f : C.Hom B C) (g : C.Hom A B) → map (f C.∘ g) D.~ (map f D.∘ map g)

instance
  open Equivalence {{...}}

  Types : Category
  Types =
    record
    { Ob = Set
    ; Hom = λ A B → A → B
    ; _~_ = λ f g → ∀ x → f x == g x
    ; ~-equiv = record
                   { reflexivity = λ x → refl
                   ; !_ = λ {f} {g} p x → ! p x
                   ; _∙_ = λ {f} {g} {h} p q r → p r ∙ q r
                   }
    ; id = λ {A} z → z
    ; _∘_ = λ {A} {B} {C} f g x → f (g x)
    ; left-id = λ {A} {B} {f} x → refl
    ; right-id = λ {A} {B} {f} x → refl
    ; assoc = λ x → refl
    }

module _ (X : Set) (T : Topology X) where
  private
    module T = Topology T

  instance
    OpenSets : Category
    OpenSets = record
      { Ob = Σ _ T.O
      ; Hom = λ U V → π₁ U ⊆ π₁ V
      ; _~_ = _==_
      ; ~-equiv = ==-equiv
      ; id = λ x z → z
      ; _∘_ = λ z z₁ x z₂ → z x (z₁ x z₂)
      ; left-id = refl
      ; right-id = refl
      ; assoc = refl
      }

  Presheaf : Set
  Presheaf = Functor (Category.opposite OpenSets) Types

  module _ (U : P X) (U-open : T.O U) where
    record Cover : Set where
      field
        Index : Set
        at : (i : Index) → P X
        at-open : (i : Index) → T.O (at i)
        at-subset : (i : Index) → at i ⊆ U
        covering : (x : X) → U x → Σ[ i ∶ Index ] at i x

    module _ (F : Presheaf) (<U> : Cover) where
      private
        module F = Functor F
        module <U> = Cover <U>

      Section : Set
      Section =
        ∀ i → F.apply (<U>.at i , <U>.at-open i)

      Coherence : Section → Set
      Coherence <s> =
        ∀ i j →
          let <U>ij = (<U>.at i ∩ <U>.at j) , (T.inter-open (<U>.at-open i) (<U>.at-open j) ) in
          F.map {<U>.at i , <U>.at-open i} {<U>ij} (λ _ → π₁) (<s> i)
            ==
          F.map {<U>.at j , <U>.at-open j} {<U>ij} (λ _ → π₂) (<s> j)

  Sheaf : Presheaf → Set
  Sheaf F =
    let module F = Functor F in
    (U : P X)
    (U-open : T.O U)
    (<U> : Cover U U-open)
    (<s> : Section U _ F <U>)
    (coh : Coherence U _  F <U> <s>)
      →
    let module <U> = Cover _ _ <U> in
      Σ![ s ∶ F.apply (U , U-open) ]
        (∀ i → F.map {U , U-open} (<U>.at-subset i) s == <s> i)

