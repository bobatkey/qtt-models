{-# OPTIONS --safe #-}

module IndexedLinear where

open import Data.Product using (_×_; Σ; proj₁; proj₂; _,_)
open import Data.Nat using (ℕ; _+_; _*_; _≤_)

⟪_⟫ : ∀ {Γ₁ Γ₂ : Set} → (Γ₁ → Γ₂) → (Γ₂ → Set) → (Γ₁ → Set)
⟪ f ⟫ A γ = A (f γ)

record IndexedPreorder : Set₂ where
  field
    Obj : Set → Set₁
    _⊢_⇒_ : (Γ : Set) → Obj Γ → Obj Γ → Set

  _⊢_≅_ : (Γ : Set) → Obj Γ → Obj Γ → Set
  Γ ⊢ X ≅ Y = (Γ ⊢ X ⇒ Y) × (Γ ⊢ Y ⇒ X)

  infix 5 _⊢_≅_ _⊢_⇒_

  field
    ⟨_⟩ : ∀ {Γ Δ} → (Γ → Δ) → Obj Δ → Obj Γ

    ⟨_⟩-map : ∀ {Γ Δ X Y} (f : Γ → Δ) → Δ ⊢ X ⇒ Y → Γ ⊢ (⟨ f ⟩ X) ⇒ (⟨ f ⟩ Y)

    ⟨id⟩  : ∀ {Γ X} → Γ ⊢ X ≅ (⟨ (λ x → x) ⟩ X)
    ⟨_∘_⟩ : ∀ {Γ₁ Γ₂ Γ₃ X} (f : Γ₂ → Γ₃) (g : Γ₁ → Γ₂) →
             Γ₁ ⊢ (⟨ g ⟩ (⟨ f ⟩ X)) ≅ (⟨ (λ x → f (g x)) ⟩ X)

    -- identities and composition
    id  : ∀ {Γ X} → Γ ⊢ X ⇒ X
    _∘_ : ∀ {Γ X Y Z} → Γ ⊢ Y ⇒ Z → Γ ⊢ X ⇒ Y → Γ ⊢ X ⇒ Z

  infixl 4 _∘_

record IndexedSMC (L : IndexedPreorder) : Set₁ where
  open IndexedPreorder L

  infixl 20 _⊗_

  field
    -- Symmetric monoidal structure
    I    : ∀ {Γ} → Obj Γ
    _⊗_  : ∀ {Γ} → Obj Γ → Obj Γ → Obj Γ
    _⊗m_ : ∀ {Γ X Y X' Y'} → Γ ⊢ X ⇒ X' → Γ ⊢ Y ⇒ Y' → Γ ⊢ X ⊗ Y ⇒ X' ⊗ Y'

    -- swapping, associativity and units
    swap  : ∀ {Γ X Y} → Γ ⊢ (X ⊗ Y) ⇒ (Y ⊗ X)
    assoc : ∀ {Γ X Y Z} → Γ ⊢ (X ⊗ (Y ⊗ Z)) ≅ ((X ⊗ Y) ⊗ Z)
    unit  : ∀ {Γ X} → Γ ⊢ (X ⊗ I) ≅ X

    -- reindexing is symmetric monoidal
    -- TODO: do these only need to be lax?
    I-subst : ∀ {Γ₁ Γ₂} (f : Γ₁ → Γ₂) → Γ₁ ⊢ ⟨ f ⟩ I ≅ I
    ⊗-subst : ∀ {Γ Δ X Y} (f : Γ → Δ) → Γ ⊢ ⟨ f ⟩ (X ⊗ Y) ≅ (⟨ f ⟩ X) ⊗ (⟨ f ⟩ Y)

    -- Closed
  field
    _⊸_ : ∀ {Γ} → Obj Γ → Obj Γ → Obj Γ
    ⊸-subst : ∀ {Γ₁ Γ₂ X Y} (f : Γ₁ → Γ₂) → Γ₁ ⊢ ⟨ f ⟩ (X ⊸ Y) ≅ ((⟨ f ⟩ X) ⊸ (⟨ f ⟩ Y))
    Λ : ∀ {Γ X Y Z} → Γ ⊢ (X ⊗ Y) ⇒ Z → Γ ⊢ X ⇒ (Y ⊸ Z)
    apply : ∀ {Γ X Y} → Γ ⊢ ((X ⊸ Y) ⊗ X) ⇒ Y

  ⊸-map : ∀ {Γ X₁ X₂ Y₁ Y₂} →
          Γ ⊢ X₂ ⇒ X₁ →
          Γ ⊢ Y₁ ⇒ Y₂ →
          Γ ⊢ (X₁ ⊸ Y₁) ⇒ (X₂ ⊸ Y₂)
  ⊸-map f g = Λ (g ∘ apply ∘ (id ⊗m f))

record IndexedProducts (L : IndexedPreorder) : Set₁ where
  open IndexedPreorder L

  field
    -- Products
    `∀       : ∀ {Γ} A → Obj (Σ Γ A) → Obj Γ
    `∀-intro : ∀ {Γ A X Y} → (Σ Γ A) ⊢ (⟨ proj₁ ⟩ X) ⇒ Y → Γ ⊢ X ⇒ (`∀ A Y)
    `∀-proj  : ∀ {Γ A X} → (Σ Γ A) ⊢ ⟨ proj₁ ⟩ (`∀ A X) ⇒ X
    `∀-subst : ∀ {Γ₁ Γ₂ A X} (f : Γ₁ → Γ₂) →
               Γ₁ ⊢ ⟨ f ⟩ (`∀ A X) ≅ `∀ (⟪ f ⟫ A) (⟨ (λ x → (f (x .proj₁)) , x .proj₂) ⟩ X)

  `∀-map : ∀ {Γ A X Y} → (Σ Γ A) ⊢ X ⇒ Y → Γ ⊢ (`∀ A X) ⇒ (`∀ A Y)
  `∀-map f = `∀-intro (f ∘ `∀-proj)

record IndexedExponential (L : IndexedPreorder) (M : IndexedSMC L) : Set₁ where
  open IndexedPreorder L
  open IndexedSMC M

  field
    -- FIXME: generalise to any suitable ordered semiring
    ![_] : ∀ {Γ} → ℕ → Obj Γ → Obj Γ   -- FIXME: why not over Γ × ℕ ???
    ![_]-map : ∀ {Γ} n {X Y} → Γ ⊢ X ⇒ Y → Γ ⊢ ![ n ] X ⇒ ![ n ] Y
    !-subst : ∀ {Γ₁ Γ₂ n A} (f : Γ₁ → Γ₂) → Γ₁ ⊢ ⟨ f ⟩ (![ n ] A) ≅ ![ n ] (⟨ f ⟩ A)
    discard : ∀ {Γ X} → Γ ⊢ ![ 0 ] X ≅ I
    comult : ∀ {Γ X m n} → Γ ⊢ ![ m ] (![ n ] X) ⇒ ![ m * n ] X
    derelict : ∀ {Γ X} → Γ ⊢ ![ 1 ] X ⇒ X
    duplicate : ∀ {Γ X m n} → Γ ⊢ ![ m + n ] X ⇒ ![ m ] X ⊗ ![ n ] X
    monoidal : ∀ {Γ X Y n} → Γ ⊢ ![ n ] X ⊗ ![ n ] Y ⇒ ![ n ] (X ⊗ Y)
    weaken : ∀ {Γ X m n} → m ≤ n → Γ ⊢ ![ n ] X ⇒ ![ m ] X
