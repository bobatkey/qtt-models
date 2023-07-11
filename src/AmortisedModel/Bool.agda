{-# OPTIONS --safe #-}

open import Algebra.ResourceMonoid

module AmortisedModel.Bool (ℳ : ResourceMonoid) (ℳ₀ : SubResourceMonoid ℳ) where

open import Data.Bool using (Bool; true; false)
open import Data.Nat using (_+_; suc; zero)
open import Data.Empty using (⊥)
open import Data.Fin using (suc; zero)
open import Data.Product using (Σ-syntax; _×_; Σ; _,_; proj₁; proj₂)

open import AmortisedRealisabilityModel ℳ ℳ₀

open ResourceMonoid ℳ renaming (Carrier to |ℳ|)
open SubResourceMonoid ℳ₀ renaming (member to mor-potential)
open import MachineModel

`Bool : Bool -Obj
`Bool false .realises α false = 0 ≤D⟨ α , ∅ ⟩
`Bool false .realises α ⋆ = ⊥
`Bool false .realises α (_ , _) = ⊥
`Bool false .realises α true = ⊥
`Bool false .realises α (clo _ _) = ⊥
`Bool true .realises α ⋆ = ⊥
`Bool true .realises α (_ , _) = ⊥
`Bool true .realises α true = 0 ≤D⟨ α , ∅ ⟩
`Bool true .realises α false = ⊥
`Bool true .realises α (clo _ _) = ⊥

K : ∀ {A B : Set} → A → B → A
K a _ = a

`true : ∀ {Γ} → Γ ⊢ I ⇒ (⟨ K true ⟩ `Bool)
`true .realiser .expr _ = true
`true .realiser .potential = acct 1
`true .realiser .potential-ok = `acct
`true .realises γ η α ⋆ r .result = true
`true .realises γ η α ⋆ r .steps = 1
`true .realises γ η α ⋆ r .result-potential = ∅
`true .realises γ η α ⋆ r .evaluation = true
`true .realises γ η α ⋆ r .result-realises = identity
`true .realises γ η α ⋆ r .accounted = acct⊕- ； r

`false : ∀ {Γ} → Γ ⊢ I ⇒ (⟨ K false ⟩ `Bool)
`false .realiser .expr _ = false
`false .realiser .potential = acct 1
`false .realiser .potential-ok = `acct
`false .realises γ η α ⋆ r .result = false
`false .realises γ η α ⋆ r .steps = 1
`false .realises γ η α ⋆ r .result-potential = ∅
`false .realises γ η α ⋆ r .evaluation = false
`false .realises γ η α ⋆ r .result-realises = identity
`false .realises γ η α ⋆ r .accounted = acct⊕- ； r

`cond : ∀ {Γ : Set}{X : Γ -Obj}{Y : (Γ × Bool) -Obj} →
        Γ ⊢ X ⇒ ⟨ κ true ⟩ Y →
        Γ ⊢ X ⇒ ⟨ κ false ⟩ Y →
        (Γ × Bool) ⊢ ⟨ proj₁ ⟩ X ⊗ ⟨ proj₂ ⟩ `Bool ⇒ Y
`cond on-true on-false .realiser .expr n =
  letpair zero then
  cond zero then (seq ` suc zero then on-true .realiser .expr (3 + n))
            else (seq ` suc zero then on-false .realiser .expr (3 + n))
`cond on-true on-false .realiser .potential =
  acct 4 ⊕ on-true .realiser .potential ⊕ on-false .realiser .potential
`cond on-true on-false .realiser .potential-ok =
  (`acct `⊕ on-true .realiser .potential-ok) `⊕ on-false .realiser .potential-ok
`cond on-true on-false .realises (γ , false) η α (vx , false) (α₁ , α₂ , d , vx-r , b-r) =
  is-realisable
  where
    r = on-false .realises γ (η ,- _ ,- _ ,- _) α₁ vx vx-r

    is-realisable : Eval _ _ _ _
    is-realisable .result = r .result
    is-realisable .steps = 4 + r .steps
    is-realisable .result-potential = r .result-potential
    is-realisable .evaluation =
      letpair zero (cond-false zero (seq (access (suc zero)) (r .evaluation)))
    is-realisable .result-realises = r .result-realises
    is-realisable .accounted =
      assoc-inv ； pair (acct⊕- ； term) ； unit' ； pair' d' ； r .accounted
      where
        d' : 0 ≤D⟨ α , α₁ ⟩
        d' = d ； pair' b-r ； unit
`cond on-true on-false .realises (γ , true) η α (vx , true) (α₁ , α₂ , d , vx-r , b-r) =
  is-realisable
  where
    r = on-true .realises γ (η ,- _ ,- _ ,- _) α₁ vx vx-r

    is-realisable : Eval _ _ _ _
    is-realisable .result = r .result
    is-realisable .steps = 4 + r .steps
    is-realisable .result-potential = r .result-potential
    is-realisable .evaluation =
      letpair zero (cond-true zero (seq (access (suc zero)) (r .evaluation)))
    is-realisable .result-realises = r .result-realises
    is-realisable .accounted =
      assoc-inv ；
      assoc-inv ；
      acct⊕- ；
      pair' (pair term ； unit') ；
      pair' d' ；
      r .accounted
      where
        d' : 0 ≤D⟨ α , α₁ ⟩
        d' = d ； pair' b-r ； unit
