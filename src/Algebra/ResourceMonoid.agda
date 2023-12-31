{-# OPTIONS --safe #-}

module Algebra.ResourceMonoid where

open import Data.Nat as ℕ using (ℕ; _+_; _≤_; zero; suc; _*_)
import Data.Nat.Properties as ℕ
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (sym)

record ResourceMonoid : Set₁ where
  field
   Carrier   : Set
   ∅        : Carrier
   _⊕_      : Carrier → Carrier → Carrier
   _≤D⟨_,_⟩ : ℕ → Carrier → Carrier → Set
   acct     : ℕ → Carrier

   identity  : ∀ {m}           → 0 ≤D⟨ m , m ⟩
   _；_       : ∀ {k₁ k₂ m n l} → k₁ ≤D⟨ m , n ⟩ → k₂ ≤D⟨ n , l ⟩ → (k₁ + k₂) ≤D⟨ m , l ⟩
   weaken    : ∀ {k₁ k₂ m n}   → k₁ ≤D⟨ m , n ⟩ → k₂ ≤ k₁ → k₂ ≤D⟨ m , n ⟩
   pair      : ∀ {k m n l}    → k ≤D⟨ m , n ⟩ → k ≤D⟨ m ⊕ l , n ⊕ l ⟩
   symmetry  : ∀ {m n}        → 0 ≤D⟨ m ⊕ n , n ⊕ m ⟩
   unit      : ∀ {m}          → 0 ≤D⟨ m ⊕ ∅ , m ⟩
   unit-inv  : ∀ {m}          → 0 ≤D⟨ m , m ⊕ ∅ ⟩
   assoc     : ∀ {m n l}      → 0 ≤D⟨ m ⊕ (n ⊕ l) , (m ⊕ n) ⊕ l ⟩
   assoc-inv : ∀ {m n l}      → 0 ≤D⟨ (m ⊕ n) ⊕ l , m ⊕ (n ⊕ l) ⟩
   term      : ∀ {m}          → 0 ≤D⟨ m , ∅ ⟩
   account   : ∀ {k}          → k ≤D⟨ acct k , ∅ ⟩

  pair'      : ∀ {k m n l}    → k ≤D⟨ m , n ⟩ → k ≤D⟨ l ⊕ m , l ⊕ n ⟩
  pair' f = weaken (symmetry ； pair f ； symmetry) (ℕ.≤-reflexive (sym (ℕ.+-identityʳ _)))

  unit' : ∀ {m} → 0 ≤D⟨ ∅ ⊕ m , m ⟩
  unit' = symmetry ； unit

  unit'-inv : ∀ {m} → 0 ≤D⟨ m , ∅ ⊕ m ⟩
  unit'-inv = unit-inv ； symmetry

  snd : ∀ m n → 0 ≤D⟨ m ⊕ n , n ⟩
  snd m n = pair term ； symmetry ； unit

  fst : ∀ {m n} → 0 ≤D⟨ m ⊕ n , m ⟩
  fst = pair' term ； unit

  repeat : ℕ → Carrier → Carrier
  repeat zero    m = ∅
  repeat (suc n) m = m ⊕ repeat n m

  repeat-f' : ∀ {α β k} m → k ≤D⟨ α , β ⟩ → (m * k) ≤D⟨ repeat m α , repeat m β ⟩
  repeat-f' zero f = identity
  repeat-f' (suc m) f = pair f ； pair' (repeat-f' m f)

  repeat-f : ∀ {α β} m → 0 ≤D⟨ α , β ⟩ → 0 ≤D⟨ repeat m α , repeat m β ⟩
  repeat-f zero f = identity
  repeat-f (suc m) f = pair' (repeat-f m f)  ； pair f

  repeat-monoidal : ∀ {α β} n → 0 ≤D⟨ repeat n α ⊕ repeat n β , repeat n (α ⊕ β) ⟩
  repeat-monoidal zero = term
  repeat-monoidal (suc n) =
    assoc-inv ； pair' assoc ； pair' (pair symmetry) ； pair' assoc-inv ； assoc ； pair' (repeat-monoidal n)

  repeat-add : ∀ {α} m n → 0 ≤D⟨ repeat m α ⊕ repeat n α , repeat (m + n) α ⟩
  repeat-add zero n = unit'
  repeat-add (suc m) n = assoc-inv ； pair' (repeat-add m n)

  repeat-add-inv : ∀ {α} m n → 0 ≤D⟨ repeat (m + n) α , repeat m α ⊕ repeat n α ⟩
  repeat-add-inv zero n = unit'-inv
  repeat-add-inv (suc m) n = pair' (repeat-add-inv m n) ； assoc

  repeat-wk : ∀ {α m n} → m ≤ n → 0 ≤D⟨ repeat n α , repeat m α ⟩
  repeat-wk ℕ.z≤n       = term
  repeat-wk (ℕ.s≤s m≤n) = pair' (repeat-wk m≤n)

  repeat-mul : ∀ {α} m n → 0 ≤D⟨ repeat m (repeat n α) , repeat (m * n) α ⟩
  repeat-mul zero n = identity
  repeat-mul (suc m) n =
    pair' (repeat-mul m n) ； (repeat-add n (m * n))

  acct⊕- : ∀ {k α} → k ≤D⟨ acct k ⊕ α , α ⟩
  acct⊕- = weaken (pair account ； (symmetry ； unit)) (ℕ.≤-reflexive (sym (ℕ.+-identityʳ _)))

  infixl 50 _；_
  infixl 30 _⊕_

record SubResourceMonoid (M : ResourceMonoid) : Set₁ where
  open ResourceMonoid M
  field
    member : Carrier → Set
    _`⊕_   : ∀ {x y} → member x → member y → member (x ⊕ y)
    `∅     : member ∅
    `acct  : ∀ {k} → member (acct k)

  `repeat : ∀ n α → member α → member (repeat n α)
  `repeat zero α α-member = `∅
  `repeat (suc n) α α-member = α-member `⊕ (`repeat n α α-member)

module _ where
  open SubResourceMonoid

  entire : ∀ M → SubResourceMonoid M
  entire M .member α = ⊤
  entire M ._`⊕_ tt tt = tt
  entire M .`∅ = tt
  entire M .`acct = tt
