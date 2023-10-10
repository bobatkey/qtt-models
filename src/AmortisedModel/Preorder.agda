{-# OPTIONS --safe #-}

open import Algebra.ResourceMonoid

module AmortisedModel.Preorder (ℳ : ResourceMonoid) (ℳ₀ : SubResourceMonoid ℳ) where

open import Data.Fin using (suc; zero)
open import Data.Nat using (ℕ; suc; zero; _+_; _*_; _≤_)
open import Data.Nat.Properties using (≤-reflexive)
open import Data.Nat.Solver using (module +-*-Solver)
open import Data.Product using (Σ-syntax; _×_; Σ; _,_; proj₁; proj₂)

open import AmortisedModel.Machine

open ResourceMonoid ℳ renaming (Carrier to |ℳ|)
open SubResourceMonoid ℳ₀ renaming (member to mor-potential)

record Elem : Set₁ where
  field
    realises : |ℳ| → val → Set
open Elem public

_-Obj : Set → Set₁
Γ -Obj = Γ → Elem

record Eval {n} (Y : Elem) (e : exp n) (α : |ℳ|) (η : env n) : Set where
  field
    result           : val
    steps            : ℕ
    result-potential : |ℳ|
    evaluation       : e , η ⇓[ steps ] result
    result-realises  : Y .realises result-potential result
    accounted        : steps ≤D⟨ α , result-potential ⟩
open Eval public

record Realiser : Set where
  field
    expr         : ∀ n → exp (suc n)
    potential    : |ℳ|
    potential-ok : mor-potential potential
open Realiser public

record _⊢_⇒_ (Γ : Set) (X Y : Γ → Elem) : Set where
  field
    realiser : Realiser
    realises : ∀ γ → ∀ {n} (η : env n) (α : |ℳ|) v →
               X γ .realises α v →
               Eval (Y γ) (realiser .expr n) (realiser .potential ⊕ α) (η ,- v)
open _⊢_⇒_ public

_⊢_≅_ : (Γ : Set) → Γ -Obj → Γ -Obj → Set
Γ ⊢ X ≅ Y = (Γ ⊢ X ⇒ Y) × (Γ ⊢ Y ⇒ X)

infix 21 ⟨_⟩_
infix 5 _⊢_≅_ _⊢_⇒_

------------------------------------------------------------------------------
identity-realiser : Realiser
identity-realiser .expr _ = ` zero
identity-realiser .potential = acct 1
identity-realiser .potential-ok = `acct

identity-realises : ∀ {Γ} {X Y : Γ -Obj} →
  (∀ γ α v → X γ .realises α v → Y γ .realises α v) →
  ∀ γ {n} (η : env n) (α : |ℳ|) v →
  X γ .realises α v → Eval (Y γ) (` zero) (acct 1 ⊕ α) (η ,- v)
identity-realises X⊆Y γ η α v X-v .result = v
identity-realises X⊆Y γ η α v X-v .steps = 1
identity-realises X⊆Y γ η α v X-v .result-potential = α
identity-realises X⊆Y γ η α v X-v .evaluation = access zero
identity-realises X⊆Y γ η α v X-v .result-realises = X⊆Y γ α v X-v
identity-realises X⊆Y γ η α v X-v .accounted = acct⊕-

identity-realised : ∀ {Γ} {X Y : Γ -Obj} →
  (∀ γ α v → X γ .realises α v → Y γ .realises α v) →
  Γ ⊢ X ⇒ Y
identity-realised X⊆Y .realiser = identity-realiser
identity-realised X⊆Y .realises = identity-realises X⊆Y


realised-iso : ∀ {Γ} {X Y : Γ -Obj} →
  (∀ γ α v → X γ .realises α v → Y γ .realises α v) →
  (∀ γ α v → Y γ .realises α v → X γ .realises α v) →
  Γ ⊢ X ≅ Y
realised-iso X⊆Y Y⊆X .proj₁ = identity-realised X⊆Y
realised-iso X⊆Y Y⊆X .proj₂ = identity-realised Y⊆X

------------------------------------------------------------------------
-- Reindexing

⟨_⟩_ : ∀ {Γ Δ} → (Γ → Δ) → Δ -Obj → Γ -Obj
⟨ f ⟩ X = λ γ → X (f γ)

⟨_⟩-map : ∀ {Γ Δ X Y} (f : Γ → Δ) → Δ ⊢ X ⇒ Y → Γ ⊢ (⟨ f ⟩ X) ⇒ (⟨ f ⟩ Y)
⟨ f ⟩-map g .realiser = g .realiser
⟨ f ⟩-map g .realises γ η α v x = g .realises (f γ) η α v x

⟨id⟩ : ∀ {Γ X} → Γ ⊢ X ≅ (⟨ (λ x → x) ⟩ X)
⟨id⟩ = realised-iso (λ _ _ _ x → x) (λ _ _ _ x → x)

⟨_∘_⟩ : ∀ {Γ₁ Γ₂ Γ₃ X} (f : Γ₂ → Γ₃) (g : Γ₁ → Γ₂) →
        Γ₁ ⊢ (⟨ g ⟩ (⟨ f ⟩ X)) ≅ (⟨ (λ x → f (g x)) ⟩ X)
⟨ f ∘ g ⟩ = realised-iso (λ _ _ _ x → x) (λ _ _ _ x → x)

------------------------------------------------------------------------
-- Identity and composition in each fibre

id : ∀ {Γ X} → Γ ⊢ X ⇒ X
id = identity-realised (λ _ _ _ x → x)

_∘_ : ∀ {Γ X Y Z} → Γ ⊢ Y ⇒ Z → Γ ⊢ X ⇒ Y → Γ ⊢ X ⇒ Z
(f ∘ g) .realiser .expr n = seq (g .realiser .expr n) then f .realiser .expr (suc n)
(f ∘ g) .realiser .potential = acct 1 ⊕ f .realiser .potential ⊕ g .realiser .potential
(f ∘ g) .realiser .potential-ok =
   (`acct `⊕ f .realiser .potential-ok) `⊕ g .realiser .potential-ok
(f ∘ g) .realises γ η α v X-α-v = is-realisable
  where
    gr = g .realises γ η α v X-α-v
    fr = f .realises γ (η ,- v) (gr .result-potential) (gr .result) (gr .result-realises)

    is-realisable : Eval _ _ _ _
    is-realisable .result = fr .result
    is-realisable .steps = gr .steps + 1 + fr .steps
    is-realisable .result-potential = fr .result-potential
    is-realisable .evaluation = seq (gr .evaluation) (fr .evaluation)
    is-realisable .result-realises = fr .result-realises
    is-realisable .accounted =
       assoc-inv ； assoc-inv ； pair' (pair' (gr .accounted)) ； acct⊕- ； fr .accounted
