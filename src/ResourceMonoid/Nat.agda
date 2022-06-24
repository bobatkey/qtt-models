{-# OPTIONS --postfix-projections --safe --without-K #-}

module ResourceMonoid.Nat where

open import Data.Nat using (ℕ; _+_; _≤_; z≤n)
open import Data.Nat.Properties
   using (≤-refl; ≤-trans; ≤-reflexive; +-assoc; +-monoʳ-≤; +-monoˡ-≤; +-comm; +-identityʳ)
open import Relation.Binary.PropositionalEquality using (sym)
open import resource-monoid

open rmonoid

ℕ-rm : rmonoid
∣ ℕ-rm ∣ = ℕ
ℕ-rm .∅ = 0
ℕ-rm ._⊕_ = _+_
ℕ-rm ._≤D⟨_,_⟩ k m n = k + n ≤ m
ℕ-rm .acct k = k
ℕ-rm .identity = ≤-refl
ℕ-rm ._⟫_ {k₁} k₁+n≤m k₂+l≤n =
  ≤-trans (≤-trans (≤-reflexive (+-assoc k₁ _ _)) (+-monoʳ-≤ k₁ k₂+l≤n)) k₁+n≤m
ℕ-rm .weaken k₁+n≤m k₂≤k₁ = ≤-trans (+-monoˡ-≤ _ k₂≤k₁) k₁+n≤m
ℕ-rm .pair {k}{m}{n}{l} k+n≤m =
  ≤-trans (≤-reflexive (sym (+-assoc k n l))) (+-monoˡ-≤ _ k+n≤m)
ℕ-rm .symmetry {m}{n} = ≤-reflexive (+-comm n m)
ℕ-rm .unit = ≤-reflexive (sym (+-identityʳ _))
ℕ-rm .unit-inv = ≤-reflexive (+-identityʳ _)
ℕ-rm .assoc {m}{n}{l}= ≤-reflexive (+-assoc m n l)
ℕ-rm .assoc-inv {m}{n}{l} = ≤-reflexive (sym (+-assoc m n l))
ℕ-rm .term = z≤n
ℕ-rm .account = ≤-reflexive (+-identityʳ _)
