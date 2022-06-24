{-# OPTIONS --postfix-projections --safe --without-K #-}

module ConsFree where

open import Data.Nat using (ℕ; _≤_)
open import Data.Nat.Properties using (≤-refl; module ≤-Reasoning; ⊔-idem; ≤-reflexive)
open import Data.Fin using (zero; suc)
open import Data.Product using (Σ-syntax; _,_; _×_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (refl)

open import machine-model
open import resource-monoid
open import ResourceMonoid.Polynomial
open import amort-realisers
open import nat-poly using (ℕ-poly; ⟪_⟫; 0-poly)

open poly-monoid (⊔-size-algebra)

open amort-indexed-preorder (poly-monoid) (poly-monoid₀)

open import ConsFree.Iterator
   poly-monoid poly-monoid₀
   size raise {!!} scale raise→scale scale-zero scale-suc
   (duplicate-size λ n → ≤-reflexive (⊔-idem n))


{-
-- The polytime property for this calculus
poly-time : ∀ {X} →
   (f : ℕ ⊢ `nat ⇒ X) →
   Σ[ p ∈ ℕ-poly ] ∀ n →
      Σ[ v ∈ val ] Σ[ k ∈ ℕ ]
        f .realiser .expr 0 , (nil ,- nat-val n) ⇓[ k ] v
        × k ≤ ⟪ p ⟫ n
poly-time f .proj₁ = f .realiser .potential .proj₂
poly-time f .proj₂ n =
  r .result ,
  r .steps ,
  r .evaluation ,
  under-time
  where
  r = f .realises n nil (size n) (nat-val n) (refl , ≤-refl , (λ _ _ → ≤-refl))

  -- FIXME: work this out on paper
  under-time : r .steps ≤ ⟪ f .realiser .potential .proj₂ ⟫ n
  under-time =
   begin
      r .steps
    ≤⟨ {!r .accounted!} ⟩
      r .steps
    ≤⟨ {!!} ⟩
      ⟪ f .realiser .potential .proj₂ ⟫ n
    ∎
    where open ≤-Reasoning
-}
