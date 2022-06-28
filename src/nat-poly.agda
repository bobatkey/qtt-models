{-# OPTIONS --postfix-projections --safe --without-K #-}

module nat-poly where

open import Data.Nat
open import Data.Nat.Properties
open import Data.List
open import Data.Sum
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; trans; cong; subst; sym; cong₂)
open Eq.≡-Reasoning -- using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)

ℕ-poly : Set
ℕ-poly = List ℕ

-- evaluate the polynomial using Horner's method
⟪_⟫ : ℕ-poly → ℕ → ℕ
⟪ [] ⟫     x = 0
⟪ p₀ ∷ p ⟫ x = p₀ + x * ⟪ p ⟫ x

-- turns out this isn't needed
eval-mono : ∀ p x y → x ≤ y → ⟪ p ⟫ x ≤ ⟪ p ⟫ y
eval-mono []       x y x≤y = ≤-refl
eval-mono (p₀ ∷ p) x y x≤y = +-monoʳ-≤ p₀ (*-mono-≤ x≤y (eval-mono p x y x≤y))

0-poly : ℕ-poly
0-poly = []

const-poly : ℕ → ℕ-poly
const-poly n = n ∷ []

-- raise the degree of the polynomial by 1
↑_ : ℕ-poly → ℕ-poly
↑ p = 0 ∷ p

scale : ℕ → ℕ-poly → ℕ-poly
scale n []       = []
scale n (p₀ ∷ p) = (n * p₀) ∷ scale n p

_+-poly_ : ℕ-poly → ℕ-poly → ℕ-poly
_+-poly_ []       []       = []
_+-poly_ []       (b ∷ bs) = b ∷ bs
_+-poly_ (a ∷ as) []       = a ∷ as
_+-poly_ (a ∷ as) (b ∷ bs) = (a + b) ∷ (as +-poly bs)

_⊔-poly_ : ℕ-poly → ℕ-poly → ℕ-poly
_⊔-poly_ []       []       = []
_⊔-poly_ []       (b ∷ bs) = b ∷ bs
_⊔-poly_ (a ∷ as) []       = a ∷ as
_⊔-poly_ (a ∷ as) (b ∷ bs) = (a ⊔ b) ∷ (as ⊔-poly bs)

eval-scale : ∀ n p x → ⟪ scale n p ⟫ x ≡ n * ⟪ p ⟫ x
eval-scale n []       x = sym (*-zeroʳ n)
eval-scale n (p₀ ∷ p) x =
  begin
    n * p₀ + x * ⟪ scale n p ⟫ x
  ≡⟨ cong (λ □ → n * p₀ + x * □) (eval-scale n p x) ⟩
    n * p₀ + x * (n * ⟪ p ⟫ x)
  ≡⟨ cong (λ □ → n * p₀ + □) (sym (*-assoc x n (⟪ p ⟫ x)))  ⟩
    n * p₀ + (x * n) * ⟪ p ⟫ x
  ≡⟨ cong (λ □ → n * p₀ + (□ * ⟪ p ⟫ x)) (*-comm x n) ⟩
    n * p₀ + (n * x) * ⟪ p ⟫ x
  ≡⟨ cong (λ □ → n * p₀ + □) (*-assoc n x (⟪ p ⟫ x)) ⟩
    n * p₀ + n * (x * ⟪ p ⟫ x)
  ≡⟨ sym (*-distribˡ-+ n p₀ (x * ⟪ p ⟫ x)) ⟩
    n * (p₀ + x * ⟪ p ⟫ x)
  ∎

↑-wins : ∀ n p x → n ≤ x → ⟪ scale n p ⟫ x ≤ ⟪ ↑ p ⟫ x
↑-wins n p x n≤x = ≤-trans (≤-reflexive (eval-scale n p x)) (*-monoˡ-≤ _ n≤x)

-- for linear functions:
---  n*(a*x + b) = (n*a)*x + n*b

-- Problem is that there is No way of recognising that this particular
-- set of diamonds has been used up!

--   (n , p)   k ≤D⟨ (m , p) , (n , q) ⟩ ⇔  (n ≤ m) × (∀ x → m ≤ x → k + ⟪ q ⟫ n ≤ ⟪ p ⟫ x)

eval-0 : ∀ x → ⟪ 0-poly ⟫ x ≡ 0
eval-0 x = refl

eval-+ : ∀ p q x → ⟪ p +-poly q ⟫ x ≡ ⟪ p ⟫ x + ⟪ q ⟫ x
eval-+ []       []       x = refl
eval-+ []       (q₀ ∷ q) x = refl
eval-+ (p₀ ∷ p) []       x = sym (+-identityʳ _)
eval-+ (p₀ ∷ p) (q₀ ∷ q) x =
  begin
    ⟪ (p₀ ∷ p) +-poly (q₀ ∷ q) ⟫ x
  ≡⟨⟩
    (p₀ + q₀) + x * ⟪ p +-poly q ⟫ x
  ≡⟨ cong (λ □ → (p₀ + q₀) + x * □) (eval-+ p q x) ⟩
    (p₀ + q₀) + x * (⟪ p ⟫ x + ⟪ q ⟫ x)
  ≡⟨ cong (λ □ → (p₀ + q₀) + □) (*-distribˡ-+ x (⟪ p ⟫ x) (⟪ q ⟫ x)) ⟩
    (p₀ + q₀) + (x * ⟪ p ⟫ x + x * ⟪ q ⟫ x)
  ≡⟨ cong (λ □ → □ + (x * ⟪ p ⟫ x + x * ⟪ q ⟫ x)) (+-comm p₀ q₀) ⟩
    (q₀ + p₀) + (x * ⟪ p ⟫ x + x * ⟪ q ⟫ x)
  ≡⟨ +-assoc q₀ p₀ (x * ⟪ p ⟫ x + x * ⟪ q ⟫ x) ⟩
    q₀ + (p₀ + (x * ⟪ p ⟫ x + x * ⟪ q ⟫ x))
  ≡⟨ cong (λ □ → q₀ + □) (sym (+-assoc p₀ (x * ⟪ p ⟫ x) (x * ⟪ q ⟫ x))) ⟩
    q₀ + ((p₀ + x * ⟪ p ⟫ x) + x * ⟪ q ⟫ x)
  ≡⟨ +-comm q₀ ((p₀ + x * ⟪ p ⟫ x) + x * ⟪ q ⟫ x) ⟩
    ((p₀ + x * ⟪ p ⟫ x) + x * ⟪ q ⟫ x) + q₀
  ≡⟨ +-assoc (p₀ + x * ⟪ p ⟫ x) (x * ⟪ q ⟫ x) q₀ ⟩
    (p₀ + x * ⟪ p ⟫ x) + (x * ⟪ q ⟫ x + q₀)
  ≡⟨ cong (λ □ → (p₀ + x * ⟪ p ⟫ x) + □) (+-comm (x * ⟪ q ⟫ x) q₀) ⟩
    (p₀ + x * ⟪ p ⟫ x) + (q₀ + x * ⟪ q ⟫ x)
  ≡⟨⟩
    ⟪ p₀ ∷ p ⟫ x + ⟪ q₀ ∷ q ⟫ x
  ∎

{-
dist : ∀ a b c → a * (b ⊔ c) ≡ (a * b) ⊔ (a * c)
dist a b c with ⊔-sel b c
... | inj₁ b⊔c≡b = begin
                      a * (b ⊔ c)
                    ≡⟨ cong (λ □ → a * □) b⊔c≡b ⟩
                      a * b
                    ≡⟨ sym (m≥n⇒m⊔n≡m (*-monoʳ-≤ a (m⊔n≡m⇒n≤m b⊔c≡b))) ⟩
                      (a * b) ⊔ (a * c)
                    ∎
... | inj₂ b⊔c≡c = begin
                      a * (b ⊔ c)
                    ≡⟨ cong (λ □ → a * □) b⊔c≡c ⟩
                      a * c
                    ≡⟨ sym (m≤n⇒m⊔n≡n (*-monoʳ-≤ a (m⊔n≡n⇒m≤n b⊔c≡c))) ⟩
                      (a * b) ⊔ (a * c)
                    ∎
-}
-- Have that p ⊔-poly q is an upper bound of p and q, but not the
-- least (which isn't necessarily expressible as a polynomial because
-- it might be discontinuous)

-- eval-⊔ : ∀ p q x → ⟪ p ⟫ x ≤ ⟪ p ⊔-poly q ⟫ x
-- eval-⊔ p q x = ?

scale-1 : ∀ p x → ⟪ scale 1 p ⟫ x ≡ ⟪ p ⟫ x
scale-1 p x =
  begin
    ⟪ scale 1 p ⟫ x
  ≡⟨ eval-scale 1 p x ⟩
    1 * ⟪ p ⟫ x
  ≡⟨ *-identityˡ (⟪ p ⟫ x) ⟩
    ⟪ p ⟫ x
  ∎

scale-+ : ∀ m n p x → ⟪ scale (m + n) p ⟫ x ≡ ⟪ scale m p +-poly scale n p ⟫ x
scale-+ m n p x =
  begin
    ⟪ scale (m + n) p ⟫ x
  ≡⟨ eval-scale (m + n) p x ⟩
    (m + n) * ⟪ p ⟫ x
  ≡⟨ *-distribʳ-+ (⟪ p ⟫ x) m n ⟩
    m * ⟪ p ⟫ x + n * ⟪ p ⟫ x
  ≡⟨ cong₂ _+_ (sym (eval-scale m p x)) (sym (eval-scale n p x)) ⟩
    ⟪ scale m p ⟫ x + ⟪ scale n p ⟫ x
  ≡⟨ sym (eval-+ (scale m p) (scale n p) x) ⟩
    ⟪ scale m p +-poly scale n p ⟫ x
  ∎

comm : ∀ p q x → ⟪ p +-poly q ⟫ x ≡ ⟪ q +-poly p ⟫ x
comm p q x =
  begin
    ⟪ p +-poly q ⟫ x
  ≡⟨ eval-+ p q x ⟩
    ⟪ p ⟫ x + ⟪ q ⟫ x
  ≡⟨ +-comm (⟪ p ⟫ x) (⟪ q ⟫ x) ⟩
    ⟪ q ⟫ x + ⟪ p ⟫ x
  ≡⟨ sym (eval-+ q p x) ⟩
    ⟪ q +-poly p ⟫ x
  ∎

unit : ∀ p x → ⟪ p ⟫ x ≡ ⟪ p +-poly 0-poly ⟫ x
unit p x =
  begin
    ⟪ p ⟫ x
  ≡⟨ sym (+-identityʳ (⟪ p ⟫ x)) ⟩
    ⟪ p ⟫ x + 0
  ≡⟨⟩
    ⟪ p ⟫ x + ⟪ 0-poly ⟫ x
  ≡⟨ sym (eval-+ p 0-poly x) ⟩
    ⟪ p +-poly 0-poly ⟫ x
  ∎

assoc : ∀ p q r x → ⟪ (p +-poly q) +-poly r ⟫ x ≡ ⟪ p +-poly (q +-poly r) ⟫ x
assoc p q r x =
  begin
    ⟪ (p +-poly q) +-poly r ⟫ x
  ≡⟨ eval-+ (p +-poly q) r x ⟩
    ⟪ p +-poly q ⟫ x + ⟪ r ⟫ x
  ≡⟨ cong (λ □ → □ + ⟪ r ⟫ x) (eval-+ p q x) ⟩
    (⟪ p ⟫ x + ⟪ q ⟫ x) + ⟪ r ⟫ x
  ≡⟨ +-assoc (⟪ p ⟫ x) (⟪ q ⟫ x) (⟪ r ⟫ x) ⟩
    ⟪ p ⟫ x + (⟪ q ⟫ x + ⟪ r ⟫ x)
  ≡⟨ cong (λ □ → ⟪ p ⟫ x + □) (sym (eval-+ q r x)) ⟩
    ⟪ p ⟫ x + ⟪ q +-poly r ⟫ x
  ≡⟨ sym (eval-+ p (q +-poly r) x) ⟩
    ⟪ p +-poly (q +-poly r) ⟫ x
  ∎

{-
n-sum : ℕ → ℕ-poly → ℕ-poly
n-sum zero    p = 0-poly
n-sum (suc n) p = p +-poly n-sum n p
-}
