{-# OPTIONS --safe #-}

open import Algebra

module Interchange {c}{ℓ} (M : CommutativeMonoid c ℓ) where

open CommutativeMonoid M renaming (Carrier to |M|)

interchange : ∀ a b c d → (a ∙ b) ∙ (c ∙ d) ≈ (a ∙ c) ∙ (b ∙ d)
interchange a b c d =
  begin
    (a ∙ b) ∙ (c ∙ d)
  ≈⟨ assoc a b (c ∙ d) ⟩
    a ∙ (b ∙ (c ∙ d))
  ≈⟨ ∙-cong refl (sym (assoc b c d)) ⟩
    a ∙ ((b ∙ c) ∙ d)
  ≈⟨ ∙-cong refl (∙-cong (comm b c) refl) ⟩
    a ∙ ((c ∙ b) ∙ d)
  ≈⟨ ∙-cong refl (assoc c b d) ⟩
    a ∙ (c ∙ (b ∙ d))
  ≈⟨ sym (assoc a c (b ∙ d)) ⟩
    (a ∙ c) ∙ (b ∙ d)
  ∎
  where open import Relation.Binary.Reasoning.Setoid setoid
