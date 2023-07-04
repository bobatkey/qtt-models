{-# OPTIONS --safe #-}

open import Algebra using (CommutativeSemiring)

module Data.Polynomial {c} {ℓ} (R : CommutativeSemiring c ℓ) where

open import Level using (_⊔_)
open import Data.List using (List; []; _∷_)

open CommutativeSemiring R renaming (Carrier to |R|)

------------------------------------------------------------------------------

Poly : Set c
Poly = List |R|

-- Evaluation using "Horner's method"
⟦_⟧ : Poly → |R| → |R|
⟦ [] ⟧ x = 0#
⟦ c ∷ p ⟧ x = c + x * ⟦ p ⟧ x

_≃_ : Poly → Poly → Set (c ⊔ ℓ)
p ≃ q = ∀ x → ⟦ p ⟧ x ≈ ⟦ q ⟧ x

infix 4 _≃_

------------------------------------------------------------------------------
-- Operations

infixr 25 _·_
infixl 20 _⊕_

0-poly : Poly
0-poly = []

const : |R| → Poly
const x = x ∷ []

-- Raise the degree of the polynomial by one
↑ : Poly → Poly
↑ p = 0# ∷ p

_·_ : |R| → Poly → Poly
x · [] = []
x · (y ∷ p) = x * y ∷ x · p

_⊕_ : Poly → Poly → Poly
[] ⊕ [] = []
[] ⊕ (y ∷ q) = y ∷ q
(x ∷ p) ⊕ [] = x ∷ p
(x ∷ p) ⊕ (y ∷ q) = x + y ∷ p ⊕ q

------------------------------------------------------------------------------
open import Relation.Binary.Reasoning.Setoid setoid

eval-const : ∀ r x → ⟦ const r ⟧ x ≈ r
eval-const r x =
  begin
    ⟦ const r ⟧ x  ≡⟨⟩
    r + x * 0#     ≈⟨ +-cong refl (zeroʳ x) ⟩
    r + 0#         ≈⟨ +-identityʳ r ⟩
    r              ∎

eval-· : ∀ r p x → ⟦ r · p ⟧ x ≈ r * ⟦ p ⟧ x
eval-· r [] x = sym (zeroʳ r)
eval-· r (y ∷ p) x =
  begin
    ⟦ r · (y ∷ p) ⟧ x             ≡⟨⟩
    r * y + x * ⟦ r · p ⟧ x       ≈⟨ +-cong refl (*-cong refl (eval-· r p x)) ⟩
    r * y + x * (r * ⟦ p ⟧ x)     ≈⟨ +-cong refl (sym (*-assoc x r (⟦ p ⟧ x))) ⟩
    r * y + (x * r) * ⟦ p ⟧ x     ≈⟨ +-cong refl (*-cong (*-comm x r) refl) ⟩
    r * y + (r * x) * ⟦ p ⟧ x     ≈⟨ +-cong refl (*-assoc r x (⟦ p ⟧ x)) ⟩
    r * y + r * (x * ⟦ p ⟧ x)     ≈⟨ sym (distribˡ r y (x * ⟦ p ⟧ x)) ⟩
    r * (y + x * ⟦ p ⟧ x)         ≡⟨⟩
    r * ⟦ y ∷ p ⟧ x              ∎

eval-⊕ : ∀ p q x → ⟦ p ⊕ q ⟧ x ≈ ⟦ p ⟧ x + ⟦ q ⟧ x
eval-⊕ []      []       x = sym (+-identityʳ _)
eval-⊕ []      (_ ∷ q)  x = sym (+-identityˡ _)
eval-⊕ (_ ∷ p) []       x = sym (+-identityʳ _)
eval-⊕ (y ∷ p) (z ∷ q) x =
  begin
    ⟦ (y ∷ p) ⊕ (z ∷ q) ⟧ x              ≡⟨⟩
    y + z + x * ⟦ p ⊕ q ⟧ x               ≈⟨ +-cong refl (*-cong refl (eval-⊕ p q x)) ⟩
    y + z + x * (⟦ p ⟧ x + ⟦ q ⟧ x)       ≈⟨ +-cong refl (distribˡ x (⟦ p ⟧ x) (⟦ q ⟧ x)) ⟩
    (y + z) + (x * ⟦ p ⟧ x + x * ⟦ q ⟧ x) ≈⟨ interchange _ _ _ _ ⟩
    y + x * ⟦ p ⟧ x + (z + x * ⟦ q ⟧ x)   ≡⟨⟩
    ⟦ y ∷ p ⟧ x + ⟦ z ∷ q ⟧ x            ∎
  where open import Interchange +-commutativeMonoid

---- FIXME: how to do the order? Rely on the natural order?
-- ↑-wins : ∀ n p x → n ≤ x → ⟦ n · p ⟧ x ≤ ⟦ ↑ p ⟧ x
-- ↑-wins = ?

-- could define (using natural ordering?)
--    p ≤ q = Σ[ n ∈ |R| ] ∀ x → n ≤ x → ⟦ p ⟧ x ≤ ⟦ q ⟧ x
-- then
--    ↑-wins : ∀ r p → r · p ≤ ↑ p

·-cong : ∀ {r₁ r₂ p₁ p₂} → r₁ ≈ r₂ → p₁ ≃ p₂ → r₁ · p₁ ≃ r₂ · p₂
·-cong {r₁}{r₂}{p₁}{p₂} r₁≈r₂ p₁≃p₂ x =
  begin
    ⟦ r₁ · p₁ ⟧ x    ≈⟨ eval-· r₁ p₁ x ⟩
    r₁ * ⟦ p₁ ⟧ x    ≈⟨ *-cong r₁≈r₂ (p₁≃p₂ x) ⟩
    r₂ * ⟦ p₂ ⟧ x    ≈⟨ sym (eval-· r₂ p₂ x) ⟩
    ⟦ r₂ · p₂ ⟧ x    ∎

⊕-cong : ∀ {p₁ p₂ q₁ q₂} → p₁ ≃ p₂ → q₁ ≃ q₂ → p₁ ⊕ q₁ ≃ p₂ ⊕ q₂
⊕-cong {p₁}{p₂}{q₁}{q₂} p₁≃p₂ q₁≃q₂ x =
  begin
    ⟦ p₁ ⊕ q₁ ⟧ x        ≈⟨ eval-⊕ p₁ q₁ x ⟩
    ⟦ p₁ ⟧ x + ⟦ q₁ ⟧ x  ≈⟨ +-cong (p₁≃p₂ x) (q₁≃q₂ x) ⟩
    ⟦ p₂ ⟧ x + ⟦ q₂ ⟧ x  ≈⟨ sym (eval-⊕ p₂ q₂ x) ⟩
    ⟦ p₂ ⊕ q₂ ⟧ x        ∎

scale-1 : ∀ p → 1# · p ≃ p
scale-1 p x =
  begin
    ⟦ 1# · p ⟧ x  ≈⟨ eval-· 1# p x ⟩
    1# * ⟦ p ⟧ x  ≈⟨ *-identityˡ _ ⟩
    ⟦ p ⟧ x       ∎

scale-+ : ∀ r s p → (r + s) · p ≃ r · p ⊕ s · p
scale-+ r s p x =
  begin
    ⟦ (r + s) · p ⟧ x          ≈⟨ eval-· (r + s) p x ⟩
    (r + s) * ⟦ p ⟧ x          ≈⟨ distribʳ (⟦ p ⟧ x) r s ⟩
    r * ⟦ p ⟧ x + s * ⟦ p ⟧ x  ≈⟨ sym (+-cong (eval-· r p x) (eval-· s p x)) ⟩
    ⟦ r · p ⟧ x + ⟦ s · p ⟧ x  ≈⟨ sym (eval-⊕ (r · p) (s · p) x) ⟩
    ⟦ r · p ⊕ s · p ⟧ x       ∎

scale-⊕ : ∀ r p q → r · (p ⊕ q) ≃ r · p ⊕ r · q
scale-⊕ r p q x =
  begin
    ⟦ r · (p ⊕ q) ⟧ x           ≈⟨ eval-· r (p ⊕ q) x ⟩
    r * ⟦ p ⊕ q ⟧ x             ≈⟨ *-cong refl (eval-⊕ p q x) ⟩
    r * (⟦ p ⟧ x + ⟦ q ⟧ x)     ≈⟨ distribˡ r (⟦ p ⟧ x) (⟦ q ⟧ x) ⟩
    r * ⟦ p ⟧ x + r * ⟦ q ⟧ x   ≈⟨ sym (+-cong (eval-· r p x) (eval-· r q x)) ⟩
    ⟦ r · p ⟧ x + ⟦ r · q ⟧ x   ≈⟨ sym (eval-⊕ (r · p) (r · q) x) ⟩
    ⟦ r · p ⊕ r · q ⟧ x         ∎

scale-* : ∀ r s p → (r * s) · p ≃ r · s · p
scale-* r s p x =
  begin
    ⟦ (r * s) · p ⟧ x ≈⟨ eval-· (r * s) p x ⟩
    (r * s) * ⟦ p ⟧ x ≈⟨ *-assoc r s (⟦ p ⟧ x) ⟩
    r * (s * ⟦ p ⟧ x) ≈⟨ *-cong refl (sym (eval-· s p x)) ⟩
    r * ⟦ s · p ⟧ x   ≈⟨ sym (eval-· r (s · p) x) ⟩
    ⟦ r · s · p ⟧ x   ∎

⊕-comm : ∀ p q → p ⊕ q ≃ q ⊕ p
⊕-comm p q x =
  begin
    ⟦ p ⊕ q ⟧ x              ≈⟨ eval-⊕ p q x ⟩
    ⟦ p ⟧ x + ⟦ q ⟧ x         ≈⟨ +-comm (⟦ p ⟧ x) (⟦ q ⟧ x) ⟩
    ⟦ q ⟧ x + ⟦ p ⟧ x         ≈⟨ sym (eval-⊕ q p x) ⟩
    ⟦ q ⊕ p ⟧ x              ∎

⊕-assoc : ∀ p q r → (p ⊕ q) ⊕ r ≃ p ⊕ (q ⊕ r)
⊕-assoc p q r x =
  begin
    ⟦ (p ⊕ q) ⊕ r ⟧ x               ≈⟨ eval-⊕ (p ⊕ q) r x ⟩
    ⟦ p ⊕ q ⟧ x + ⟦ r ⟧ x            ≈⟨ +-cong (eval-⊕ p q x) refl ⟩
    (⟦ p ⟧ x + ⟦ q ⟧ x) + ⟦ r ⟧ x    ≈⟨ +-assoc _ _ _ ⟩
    ⟦ p ⟧ x + (⟦ q ⟧ x + ⟦ r ⟧ x)    ≈⟨ sym (+-cong refl (eval-⊕ q r x)) ⟩
    ⟦ p ⟧ x + ⟦ q ⊕ r ⟧ x            ≈⟨ sym (eval-⊕ p (q ⊕ r) x) ⟩
    ⟦ p ⊕ (q ⊕ r) ⟧ x               ∎

⊕-identityˡ : ∀ p → 0-poly ⊕ p ≃ p
⊕-identityˡ p x =
  begin
    ⟦ 0-poly ⊕ p ⟧ x       ≈⟨ eval-⊕ 0-poly p x ⟩
    ⟦ 0-poly ⟧ x + ⟦ p ⟧ x  ≡⟨⟩
    0# + ⟦ p ⟧ x            ≈⟨ +-identityˡ (⟦ p ⟧ x) ⟩
    ⟦ p ⟧ x                 ∎

⊕-identityʳ : ∀ p → p ⊕ 0-poly ≃ p
⊕-identityʳ p x =
  begin
    ⟦ p ⊕ 0-poly ⟧ x   ≈⟨ ⊕-comm p 0-poly x ⟩
    ⟦ 0-poly ⊕ p ⟧ x   ≈⟨ ⊕-identityˡ p x ⟩
    ⟦ p ⟧ x            ∎
