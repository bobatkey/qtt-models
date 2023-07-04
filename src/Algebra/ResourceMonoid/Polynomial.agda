{-# OPTIONS --safe #-}

{- Generic construction of ResourceMonoids with polynomial function potential -}

module Algebra.ResourceMonoid.Polynomial where

open import Data.Nat using (ℕ; _≤_; _+_; _⊔_; z≤n; zero; suc; _*_)
open import Data.Nat.Properties
   using (≤-refl; ≤-trans; ≤-reflexive;
          +-mono-≤; +-assoc; +-comm; +-identityʳ; m+n≤o⇒m≤o;
          ⊔-mono-≤; ⊔-assoc; ⊔-comm; ⊔-identityʳ; m⊔n≤o⇒m≤o;
          +-monoʳ-≤; +-monoˡ-≤; *-zeroʳ)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; sym; cong; trans; cong₂; refl)
open import Algebra.ResourceMonoid

record SizeAlgebra : Set where
  field
    _⊎_       : ℕ → ℕ → ℕ
    mono      : ∀ {x y} z → x ≤ y → (x ⊎ z) ≤ (y ⊎ z)
    assoc     : ∀ x y z → (x ⊎ y) ⊎ z ≡ x ⊎ (y ⊎ z)
    comm      : ∀ x y   → x ⊎ y ≡ y ⊎ x
    unit      : ∀ x     → x ⊎ 0 ≡ x
    bounded   : ∀ x y {z} → x ⊎ y ≤ z → x ≤ z

  interchange : ∀ a b c d → (a ⊎ b) ⊎ (c ⊎ d) ≡ (a ⊎ c) ⊎ (b ⊎ d)
  interchange a b c d =
    begin
      (a ⊎ b) ⊎ (c ⊎ d)
    ≡⟨ assoc a b (c ⊎ d) ⟩
      a ⊎ (b ⊎ (c ⊎ d))
    ≡⟨ cong (λ □ → a ⊎ □) (sym (assoc b c d)) ⟩
      a ⊎ ((b ⊎ c) ⊎ d)
    ≡⟨ cong (λ □ → a ⊎ (□ ⊎ d)) (comm b c) ⟩
      a ⊎ ((c ⊎ b) ⊎ d)
    ≡⟨ cong (λ □ → a ⊎ □) (assoc c b d) ⟩
      a ⊎ (c ⊎ (b ⊎ d))
    ≡⟨ sym (assoc a c (b ⊎ d)) ⟩
      (a ⊎ c) ⊎ (b ⊎ d)
    ∎
    where open Relation.Binary.PropositionalEquality.≡-Reasoning

+-SizeAlgebra : SizeAlgebra
+-SizeAlgebra .SizeAlgebra._⊎_ = _+_
+-SizeAlgebra .SizeAlgebra.mono z x≤y = +-mono-≤ x≤y ≤-refl
+-SizeAlgebra .SizeAlgebra.assoc x y z = +-assoc x y z
+-SizeAlgebra .SizeAlgebra.comm x y = +-comm x y
+-SizeAlgebra .SizeAlgebra.unit x = +-identityʳ x
+-SizeAlgebra .SizeAlgebra.bounded x y x⊎y≤z = m+n≤o⇒m≤o x x⊎y≤z

⊔-SizeAlgebra : SizeAlgebra
⊔-SizeAlgebra .SizeAlgebra._⊎_ = _⊔_
⊔-SizeAlgebra .SizeAlgebra.mono z x≤y = ⊔-mono-≤ x≤y ≤-refl
⊔-SizeAlgebra .SizeAlgebra.assoc x y z = ⊔-assoc x y z
⊔-SizeAlgebra .SizeAlgebra.comm x y = ⊔-comm x y
⊔-SizeAlgebra .SizeAlgebra.unit x = ⊔-identityʳ x
⊔-SizeAlgebra .SizeAlgebra.bounded x y x⊎y≤z = m⊔n≤o⇒m≤o x y x⊎y≤z

module poly-monoid (S : SizeAlgebra) where

  open import Data.Polynomial.Nat renaming (_⊕_ to _⊕p_; 0-poly to 0p)
  open SizeAlgebra S

  module monoid-defn where
    open ResourceMonoid

    -- this works for both _+_ and _⊔_: only needs the operation to be a pre-ordered commutative monoid s.t. m·n≤x → m≤x
    -- also, the class of functions only needs to be closed under constants, 0 and +
    -- and sizes needn't be natural numbers?? Could be trees? Ordinals?
    poly-monoid : ResourceMonoid
    poly-monoid .Carrier = ℕ × Poly
    poly-monoid .∅ = 0 , 0p
    poly-monoid ._⊕_ (m , p) (n , q) = m ⊎ n , p ⊕p q
    poly-monoid ._≤D⟨_,_⟩ k (m , p) (n , q) =
       (n ≤ m) × ((x : ℕ) → m ≤ x → k + ⟦ q ⟧ x ≤ ⟦ p ⟧ x)
    poly-monoid .acct n = 0 , const n
    poly-monoid .identity {n , p} =
       ≤-refl , λ x n≤x → ≤-refl
    poly-monoid ._；_ {k₁}{k₂}{m , p}{n , q}{l , r} (n≤m , ϕ₁) (l≤n , ϕ₂) =
       ≤-trans l≤n n≤m ,
       λ x m≤x → ≤-trans (≤-reflexive (+-assoc k₁ k₂ (⟦ r ⟧ x)))
                 (≤-trans (+-monoʳ-≤ k₁ (ϕ₂ x (≤-trans n≤m m≤x)))
                          (ϕ₁ x m≤x))
    poly-monoid .weaken {k₁}{k₂}{m , p}{n , q} (n≤m , ϕ) k₂≤k₁ =
       n≤m ,
       λ x m≤x → ≤-trans (+-monoˡ-≤ (⟦ q ⟧ x) k₂≤k₁) (ϕ x m≤x)
    poly-monoid .pair {k}{m , p}{n , q}{l , r} (n≤m , ϕ) =
       mono l n≤m ,
       λ x m⊔l≤x →  ≤-trans (≤-reflexive (cong (λ □ → k + □) (eval-⊕ q r x)))
                    (≤-trans (≤-reflexive (sym (+-assoc k (⟦ q ⟧ x) (⟦ r ⟧ x))))
                    (≤-trans (+-monoˡ-≤ (⟦ r ⟧ x) (ϕ x (bounded m l m⊔l≤x)))
                             (≤-reflexive (sym (eval-⊕ p r x)))))
    poly-monoid .symmetry {m , p}{n , q} =
       ≤-reflexive (comm n m) ,
       λ x _ → ≤-reflexive (⊕-comm q p x)
    poly-monoid .unit {m , p} =
      ≤-reflexive (sym (SizeAlgebra.unit S m)) ,
      λ x _ → ≤-reflexive (sym (⊕-identityʳ p x))
    poly-monoid .unit-inv {m , p} =
      ≤-reflexive (SizeAlgebra.unit S m) ,
      λ x _ → ≤-reflexive (⊕-identityʳ p x)
    poly-monoid .assoc {m , p}{n , q}{l , r} =
      ≤-reflexive (SizeAlgebra.assoc S m n l) ,
      λ x _ → ≤-reflexive (⊕-assoc p q r x)
    poly-monoid .assoc-inv {m , p}{n , q}{l , r} =
      ≤-reflexive (sym (SizeAlgebra.assoc S m n l)) ,
      λ x _ → ≤-reflexive (sym (⊕-assoc p q r x))
    poly-monoid .term {m , p} =
      z≤n ,
      λ x _ → z≤n
    poly-monoid .account {k} =
      ≤-refl ,
      λ x _ → +-monoʳ-≤ k (≤-reflexive (sym (*-zeroʳ x)))

    open SubResourceMonoid

    -- the sub-monoid of idempotently sized things
    poly-monoid-idem : SubResourceMonoid poly-monoid
    poly-monoid-idem .member (x , p) = x ⊎ x ≡ x
    poly-monoid-idem ._`⊕_ {x , _}{y , _} ϕ₁ ϕ₂ =
       trans (interchange x y x y) (cong₂ _⊎_ ϕ₁ ϕ₂)
    poly-monoid-idem .`∅ = S .unit 0
    poly-monoid-idem .`acct = S .unit 0

    poly-monoid₀ : SubResourceMonoid poly-monoid
    poly-monoid₀ .member (x , p) = x ≡ 0
    poly-monoid₀ ._`⊕_ {x , _}{y , _} refl refl = S .unit 0
    poly-monoid₀ .`∅ = refl
    poly-monoid₀ .`acct = refl

  open monoid-defn using (poly-monoid; poly-monoid₀) public
  open ResourceMonoid poly-monoid using (_≤D⟨_,_⟩; _⊕_; ∅; Carrier)

  size : ℕ → Carrier
  size n = n , 0p

  raise : Carrier → Carrier
  raise (n , p) = (n , ↑ p)

  scale : ℕ → Carrier → Carrier
  scale n (m , p) = (m , n · p)

  -- For LFPL, this only works for α that are of 0 size; in general of duplicable size
  raise→scale : ∀ α n → 0 ≤D⟨ raise α ⊕ size n , scale n α ⊕ size n ⟩
  raise→scale (m , p) n =
    ≤-refl ,
    λ x m⊔n≤x → ≤-trans (≤-reflexive (⊕-identityʳ (n · p) x))
                         (↑-wins n p x (S .SizeAlgebra.bounded n m (≤-trans (≤-reflexive (S .SizeAlgebra.comm n m)) m⊔n≤x)))

  -- this is true because ∅ is the terminal object anyway
  scale-zero : ∀ α → 0 ≤D⟨ scale zero α , ∅ ⟩
  scale-zero (m , p) =
    z≤n ,
    λ x _ → z≤n

  scale-suc : ∀ n α →
              poly-monoid₀ .SubResourceMonoid.member α →
              0 ≤D⟨ scale (1 + n) α , α ⊕ scale n α ⟩
  scale-suc n (m , p) refl =
    ≤-reflexive (S .SizeAlgebra.unit 0) ,
    λ x m≤x → ≤-reflexive (begin
                              ⟦ p ⊕p n · p ⟧ x
                            ≡⟨ eval-⊕ p (n · p) x ⟩
                              ⟦ p ⟧ x + ⟦ n · p ⟧ x
                            ≡⟨ cong (λ □ → ⟦ p ⟧ x + □) (eval-· n p x) ⟩
                              ⟦ p ⟧ x + n * ⟦ p ⟧ x
                            ≡⟨⟩
                              (1 + n) * ⟦ p ⟧ x
                            ≡⟨ sym (eval-· (1 + n) p x) ⟩
                              ⟦ (1 + n) · p ⟧ x
                            ∎)
    where open Relation.Binary.PropositionalEquality.≡-Reasoning

  -- If the ⊎ is idempotent, then we can duplicate sizes
  duplicate-size : (∀ n → n ⊎ n ≤ n) →
                   ∀ n → 0 ≤D⟨ size n , size n ⊕ size n ⟩
  duplicate-size idempotent n = idempotent n , λ _ _ → ≤-refl
