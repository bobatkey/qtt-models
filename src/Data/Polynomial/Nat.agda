{-# OPTIONS --safe #-}

module Data.Polynomial.Nat where

open import Data.Nat
open import Data.Nat.Properties

open import Data.Polynomial +-*-commutativeSemiring public

↑-wins : ∀ n p x → n ≤ x → ⟦ n · p ⟧ x ≤ ⟦ ↑ p ⟧ x
↑-wins n p x n≤x = ≤-trans (≤-reflexive (eval-· n p x)) (*-monoˡ-≤ _ n≤x)
