{-# OPTIONS --safe #-}

module LFPL where

open import Data.Nat using (ℕ; _≤_; _+_; z≤n; _⊔_; suc)
open import Data.Nat.Properties using (≤-refl; module ≤-Reasoning; ⊔-idem; ≤-reflexive; +-identityʳ; +-mono-≤; +-comm)
open import Data.Fin using (zero; suc)
open import Data.Product using (Σ-syntax; _,_; _×_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (refl; sym; cong; trans)

open import AmortisedModel.Machine
open import Algebra.ResourceMonoid
open import Algebra.ResourceMonoid.Polynomial
open import Data.Polynomial.Nat

open poly-monoid +-SizeAlgebra

open import LFPL.Iterator
   poly-monoid poly-monoid₀
   size raise
   (λ { refl → refl })
   scale raise→scale scale-zero scale-suc
   (λ n → (≤-reflexive (+-comm n 1)) , (λ _ _ → ≤-refl))
   (λ n → (≤-reflexive (+-comm 1 n)) , (λ _ _ → ≤-refl))

-- The polytime property for LFPL
poly-time : ∀ {X} →
   (f : ℕ ⊢ `nat ⇒ X) →
   Σ[ p ∈ Poly ] ∀ n →
      Σ[ v ∈ val ] Σ[ k ∈ ℕ ]
        f .realiser .expr 0 , (nil ,- nat-val n) ⇓[ k ] v
        × k ≤ ⟦ p ⟧ (suc n)
poly-time f .proj₁ = f .realiser .potential .proj₂
poly-time f .proj₂ n =
  r .result ,
  r .steps ,
  r .evaluation ,
  under-time
  where
  r = f .realises n nil (size (suc n)) (nat-val n) (refl , ≤-refl , (λ _ _ → ≤-refl))

  under-time : r .steps ≤ ⟦ f .realiser .potential .proj₂ ⟧ (suc n)
  under-time =
   begin
      r .steps
    ≡⟨ sym (+-identityʳ (r .steps)) ⟩
      r .steps + 0
    ≤⟨ +-mono-≤ ≤-refl z≤n ⟩
      r .steps + ⟦ r .result-potential .proj₂ ⟧ (suc n)
    ≤⟨ r .accounted .proj₂ (suc n) (≤-reflexive (cong (λ □ → □ + suc n) (f .realiser .potential-ok))) ⟩
      ⟦ f .realiser .potential .proj₂ ⊕ size (suc n) .proj₂ ⟧ (suc n)
    ≡⟨⟩
      ⟦ f .realiser .potential .proj₂ ⊕ 0-poly ⟧ (suc n)
    ≡⟨ ⊕-identityʳ (f .realiser .potential .proj₂) (suc n) ⟩
      ⟦ f .realiser .potential .proj₂ ⟧ (suc n)
    ∎
    where open ≤-Reasoning
