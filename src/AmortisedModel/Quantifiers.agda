{-# OPTIONS --safe #-}

open import Algebra.ResourceMonoid

module AmortisedModel.Quantifiers (ℳ : ResourceMonoid) (ℳ₀ : SubResourceMonoid ℳ) where

open import Data.Empty using (⊥)
open import Data.Fin using (suc; zero)
open import Data.Nat using (ℕ; suc; zero; _+_; _*_; _≤_)
open import Data.Product using (Σ-syntax; _×_; Σ; _,_; proj₁; proj₂)

open import MachineModel

open ResourceMonoid ℳ renaming (Carrier to |ℳ|)
open SubResourceMonoid ℳ₀ renaming (member to mor-potential)

open import AmortisedModel.Preorder ℳ ℳ₀

------------------------------------------------------------------------
-- Part V : Products

`∀ : ∀ {Γ} A → (Σ Γ A) -Obj → Γ -Obj
`∀ A X γ .realises α ⋆ = ⊥
`∀ A X γ .realises α (_ , _) = ⊥
`∀ A X γ .realises α true = ⊥
`∀ A X γ .realises α false = ⊥
`∀ A X γ .realises α (clo E η) = ∀ a v → Eval (X (γ , a)) E α (η ,- v ,- ⋆)

⟪_⟫ : ∀ {Γ₁ Γ₂ : Set} → (Γ₁ → Γ₂) → (Γ₂ → Set) → (Γ₁ → Set)
⟪ f ⟫ A γ = A (f γ)

`∀-subst : ∀ {Γ₁ Γ₂ A X} (f : Γ₁ → Γ₂) →
             Γ₁ ⊢ ⟨ f ⟩ (`∀ A X) ≅ `∀ (⟪ f ⟫ A) (⟨ (λ x → (f (x .proj₁)) , x .proj₂) ⟩ X)
`∀-subst {A = A} {X = X} f = realised-iso fwd bwd
  where
  fwd : ∀ γ α v →
        (⟨ f ⟩ `∀ A X) γ .realises α v →
        `∀ (⟪ f ⟫ A) (⟨ (λ x → f (x .proj₁) , x .proj₂) ⟩ X) γ .realises α v
  fwd γ α (clo _ _) x = x

  bwd : ∀ γ α v →
        `∀ (⟪ f ⟫ A) (⟨ (λ x → f (x .proj₁) , x .proj₂) ⟩ X) γ .realises α v →
        (⟨ f ⟩ `∀ A X) γ .realises α v
  bwd γ α (clo _ _) x = x

`∀-intro : ∀ {Γ A X Y} →
           (Σ Γ A) ⊢ (⟨ proj₁ ⟩ X) ⇒ Y →
           Γ ⊢ X ⇒ (`∀ A Y)
`∀-intro f .realiser .expr n = ƛ (seq (` (suc (suc zero))) then (f .realiser .expr _))
`∀-intro f .realiser .potential = acct 1 ⊕ (acct 2 ⊕ f .realiser .potential)
`∀-intro f .realiser .potential-ok = `acct `⊕ (`acct `⊕ f .realiser .potential-ok)
`∀-intro f .realises γ η α v X-α-v .result =
   clo (seq (` (suc (suc zero))) then (f .realiser .expr _)) (η ,- v)
`∀-intro f .realises γ η α v X-α-v .steps = 1
`∀-intro f .realises γ η α v X-α-v .result-potential = acct 2 ⊕ f .realiser .potential ⊕ α
`∀-intro f .realises γ η α v X-α-v .evaluation = lam
`∀-intro f .realises γ η α v X-α-v .result-realises a v' = is-realisable
   where
     f-r = f .realises (γ , a) (η ,- v ,- v' ,- ⋆) α v X-α-v

     is-realisable : Eval _ _ _ _
     is-realisable .result = f-r .result
     is-realisable .steps = 2 + f-r .steps
     is-realisable .result-potential = f-r .result-potential
     is-realisable .evaluation = seq (access (suc (suc zero))) (f-r .evaluation)
     is-realisable .result-realises = f-r .result-realises
     is-realisable .accounted = assoc-inv ； acct⊕- ； f-r .accounted
`∀-intro f .realises γ η α v X-α-v .accounted = assoc-inv ； acct⊕-

`∀-proj : ∀ {Γ A X} →
          (Σ Γ A) ⊢ (⟨ proj₁ ⟩ `∀ A X) ⇒ X
`∀-proj .realiser .expr _ = seq ⋆ then (suc zero · zero)
`∀-proj .realiser .potential = acct 3
`∀-proj .realiser .potential-ok = `acct
`∀-proj .realises (γ , a) η α (clo E η') E-x = is-realisable
  where
    v-r = E-x a (clo E η')

    is-realisable : Eval _ _ _ _
    is-realisable .result = v-r .result
    is-realisable .steps = 3 + v-r .steps
    is-realisable .result-potential = v-r .result-potential
    is-realisable .evaluation =
      seq mkunit (app (suc zero) zero (v-r .evaluation))
    is-realisable .result-realises = v-r .result-realises
    is-realisable .accounted = acct⊕- ； v-r .accounted

------------------------------------------------------------------------
-- Co-products

`∃ : ∀ {Γ} A → (Σ Γ A) -Obj → Γ -Obj
`∃ A X γ .realises α v = Σ[ a ∈ A γ ] X (γ , a) .realises α v

`∃-elim : ∀ {Γ A X Y} →
           (Σ Γ A) ⊢ X ⇒ (⟨ proj₁ ⟩ Y) →
           Γ ⊢ `∃ A X ⇒ Y
`∃-elim f .realiser = f .realiser
`∃-elim f .realises γ η α v (a , X-α-v) = f .realises (γ , a) η α v X-α-v

`∃-intro : ∀ {Γ A X Y} →
           Γ ⊢ `∃ A X ⇒ Y →
           (Σ Γ A) ⊢ X ⇒ (⟨ proj₁ ⟩ Y)
`∃-intro f .realiser = f .realiser
`∃-intro f .realises (γ , a) η α v X-α-v = f .realises γ η α v (a , X-α-v)
