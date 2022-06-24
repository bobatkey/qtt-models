{-# OPTIONS --postfix-projections --safe --without-K #-}

module Grothendieck where

open import Data.Product using (_×_; proj₁; proj₂; Σ; _,_)

record IndexedPreorder : Set₂ where
  field
    -- Objects
    Obj   : Set → Set₁
    -- and Morphisms
    _⊢_⇒_ : (Γ : Set) → Obj Γ → Obj Γ → Set

  _⊢_≅_ : (Γ : Set) → Obj Γ → Obj Γ → Set
  Γ ⊢ X ≅ Y = (Γ ⊢ X ⇒ Y) × (Γ ⊢ Y ⇒ X)

  field
    ⟨_⟩_ : ∀ {Γ Δ} → (Γ → Δ) → Obj Δ → Obj Γ

    ⟨_⟩-map : ∀ {Γ Δ X Y} (f : Γ → Δ) → Δ ⊢ X ⇒ Y → Γ ⊢ (⟨ f ⟩ X) ⇒ (⟨ f ⟩ Y)

    ⟨id⟩  : ∀ {Γ X} → Γ ⊢ X ≅ (⟨ (λ x → x) ⟩ X)
    ⟨_∘_⟩ : ∀ {Γ₁ Γ₂ Γ₃ X} (f : Γ₂ → Γ₃) (g : Γ₁ → Γ₂) →
             Γ₁ ⊢ (⟨ g ⟩ (⟨ f ⟩ X)) ≅ (⟨ (λ x → f (g x)) ⟩ X)

    -- identities and composition
    id  : ∀ {Γ X} → Γ ⊢ X ⇒ X
    _∘_ : ∀ {Γ X Y Z} → Γ ⊢ Y ⇒ Z → Γ ⊢ X ⇒ Y → Γ ⊢ X ⇒ Z

    -- Symmetric monoidal structure
    I    : ∀ {Γ} → Obj Γ
    _⊗_  : ∀ {Γ} → Obj Γ → Obj Γ → Obj Γ
    _⊗m_ : ∀ {Γ X Y X' Y'} → Γ ⊢ X ⇒ X' → Γ ⊢ Y ⇒ Y' → Γ ⊢ (X ⊗ Y) ⇒ (X' ⊗ Y')

    -- swapping, associativity and units
    swap  : ∀ {Γ X Y} → Γ ⊢ (X ⊗ Y) ⇒ (Y ⊗ X)
    assoc : ∀ {Γ X Y Z} → Γ ⊢ (X ⊗ (Y ⊗ Z)) ≅ ((X ⊗ Y) ⊗ Z)
    unit  : ∀ {Γ X} → Γ ⊢ (I ⊗ X) ≅ X

    -- reindexing is symmetric monoidal
    ⟨_⊗⟩ : ∀ {Γ Δ X Y} (f : Γ → Δ) → Γ ⊢ ⟨ f ⟩ (X ⊗ Y) ≅ ((⟨ f ⟩ X) ⊗ (⟨ f ⟩ Y))

    -- Closed
    _⊸_   : ∀ {Γ} → Obj Γ → Obj Γ → Obj Γ
    Λ     : ∀ {Γ X Y Z} → Γ ⊢ (X ⊗ Y) ⇒ Z → Γ ⊢ X ⇒ (Y ⊸ Z)

    -- Products
    `∀    : ∀ {Γ}(A : Γ → Set) → Obj (Σ Γ A) → Obj Γ
    `∀-intro : ∀ {Γ A X Y} → (Σ Γ A) ⊢ (⟨ proj₁ ⟩ X) ⇒ Y → Γ ⊢ X ⇒ (`∀ A Y)

    -- FIXME: need some sort of Beck-Chevalley thing...?
    -- ⟨ f ⟩ `∀ A X ≅ `∀ (A ∘ f) (⟨ f × id ⟩ X)

    -- FIXME: booleans, indexed in a certain way

    -- FIXME: graded exponentials

module Make (L : IndexedPreorder) where

  open IndexedPreorder L renaming ( Obj to _-Obj
                                  ; id  to id-L
                                  ; _∘_ to _∘-L_
                                  ; _⊗_ to _⊗L_
                                  ; swap to swap-L
                                  ; _⊸_  to _⊸L_
                                  ; Λ    to ΛL)

  record Obj : Set₂ where
    field
      Hi : Set
      Lo : Hi -Obj
  open Obj

  record _⇒_ (X Y : Obj) : Set where
    field
      mor   : X .Hi → Y .Hi
      morlo : X .Hi ⊢ X .Lo ⇒ (⟨ mor ⟩ Y .Lo)
  open _⇒_

  ------------------------------------------------------------------------
  -- Part I : Identities and Composition
  id : ∀ {X} → X ⇒ X
  id .mor x = x
  id .morlo = ⟨id⟩ .proj₁

  _∘_ : ∀ {X Y Z} → Y ⇒ Z → X ⇒ Y → X ⇒ Z
  (f ∘ g) .mor   = λ x → f .mor (g .mor x)
  (f ∘ g) .morlo = ((⟨ f .mor ∘ g .mor ⟩) .proj₁ ∘-L (⟨ g .mor ⟩-map (f .morlo))) ∘-L (g .morlo)

  ------------------------------------------------------------------------
  -- Part II : Symmetric Monoidal

  _⊗_ : Obj → Obj → Obj
  (X ⊗ Y) .Hi = X .Hi × Y .Hi
  (X ⊗ Y) .Lo = (⟨ proj₁ ⟩ X .Lo) ⊗L (⟨ proj₂ ⟩ Y .Lo)

  swap₀ : ∀ {X Y : Set} → X × Y → Y × X
  swap₀ (x , y) = (y , x)

  swap : ∀ {X Y} → (X ⊗ Y) ⇒ (Y ⊗ X)
  swap .mor = swap₀
  swap .morlo =
    (⟨ swap₀ ⊗⟩ .proj₂) ∘-L
    (((⟨ proj₁ ∘ swap₀ ⟩) .proj₂ ⊗m (⟨ proj₂ ∘ swap₀ ⟩) .proj₂) ∘-L swap-L)

  -- FIXME: bifunctorial

  -- FIXME: associativity and units

  ------------------------------------------------------------------------
  -- Part III : Closure, which relies on products
  ev : ∀ {X Y : Set} → (X → Y) × X → Y
  ev (f , x) = f x

  _⊸_ : Obj → Obj → Obj
  (X ⊸ Y) .Hi = X .Hi → Y .Hi
  (X ⊸ Y) .Lo = `∀ (λ _ → X .Hi) ((⟨ proj₂ ⟩ X .Lo) ⊸L (⟨ ev ⟩ Y .Lo))

  Λ : ∀ {X Y Z} → (X ⊗ Y) ⇒ Z → X ⇒ (Y ⊸ Z)
  Λ f .mor   = λ x y → f .mor (x , y)
  Λ f .morlo = {!`∀-intro!}

  -- FIXME: apply

  ------------------------------------------------------------------------
  -- Graded exponentials

  ------------------------------------------------------------------------
  -- Dependent type structure, as a RCwF
  record Ty (Γ : Set) : Set₂ where
    field
      Hi : Γ → Set
      Lo : (Σ Γ Hi) -Obj
  open Ty

  record RTm (Δ : Obj) (A : Ty (Δ .Hi)) : Set where
    field
      mor   : (δ : Δ .Hi) → A .Hi δ
      morlo : Δ .Hi ⊢ Δ .Lo ⇒ (⟨ (λ δ → δ , mor δ) ⟩ A .Lo)
  open RTm

  record Tm (Γ : Set) (A : Ty Γ) : Set where
    field
      mor   : (γ : Γ) → A .Hi γ
  open Tm

  -- TODO: quantitative comprehension; needs symmetric monoidal
  -- structure, and graded comonad.

  -- Context addition is EVIL! Relies on the underlying sets being
  -- equal, which is only going to work (w.o univalence) if they are
  -- constructed in an identical way.
