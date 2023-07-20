{-# OPTIONS --safe #-}

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Fin using (zero; suc)
open import Data.Nat.Properties using (module ≤-Reasoning; ≤-reflexive; +-comm)
open import Data.Product using (_×_; _,_; proj₂)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Util

open import MachineModel
open import Algebra.ResourceMonoid

module ConsFree.Iterator
    (M : ResourceMonoid) (M₀ : SubResourceMonoid M)
    (open ResourceMonoid M renaming (Carrier to |M|))
    (size         : ℕ → |M|)
    (raise        : |M| → |M|)
    (raise-ok     : ∀ {α} → M₀ .SubResourceMonoid.member α → M₀ .SubResourceMonoid.member (raise α))
    (scale        : ℕ → |M| → |M|)
    (raise→scale  : ∀ α n → 0 ≤D⟨ raise α ⊕ size n , scale n α ⊕ size n ⟩)
    (scale-zero   : ∀ α → 0 ≤D⟨ scale zero α , ∅ ⟩)
    (scale-suc    : ∀ n α → M₀ .SubResourceMonoid.member α → 0 ≤D⟨ scale (1 + n) α , α ⊕ scale n α ⟩)
    (duplicate-size : ∀ n → 0 ≤D⟨ size n , size n ⊕ size n ⟩)
      where

open import AmortisedModel.Preorder M M₀ public
open import AmortisedModel.SMC M M₀ public
open SubResourceMonoid M₀

`nat : ℕ -Obj
`nat n .realises α v = v ≡ nat-val n × 0 ≤D⟨ α , size n ⟩

duplicate-nat : ℕ ⊢ `nat ⇒ `nat ⊗ `nat
duplicate-nat .realiser .expr _ = zero , zero
duplicate-nat .realiser .potential = acct 1
duplicate-nat .realiser .potential-ok = `acct
duplicate-nat .realises n η α v (refl , α-n) = is-realisable
  where
  is-realisable : Eval _ _ _ _
  is-realisable .result = v , v
  is-realisable .steps = 1
  is-realisable .result-potential = size n
  is-realisable .evaluation = mkpair zero zero
  is-realisable .result-realises =
    size n , size n , duplicate-size n , (refl , identity) , (refl , identity)
  is-realisable .accounted = acct⊕- ； α-n

body-expr : (z s : ∀ n → exp (1 + n)) → ∀ n → exp (3 + n)
body-expr z s n =
   letpair zero then
   cond suc zero then z (4 + n)
                 else (seq (suc (suc (suc zero)) · zero) then
                       s (5 + n))

rec-expr : (z s : ∀ n → exp (1 + n)) → ∀ n → exp (suc n)
rec-expr z s n = seq (ƛ (body-expr z s n)) then (zero · suc zero)

-- Set X : Γ × ℕ → Elem = λ (γ , n) → X' (γ , n , ind z s n)

recursor : ∀ {Γ : Set}
             {X : (Γ × ℕ) -Obj} →
           Γ ⊢ I ⇒ ⟨ κ zero ⟩ X →
           (Γ × ℕ) ⊢ X ⇒ ⟨ κ-map suc ⟩ X →
           (Γ × ℕ) ⊢ ⟨ proj₂ ⟩ `nat ⇒ X
recursor z s .realiser .expr =
  rec-expr (z .realiser .expr) (s .realiser .expr)
recursor z s .realiser .potential =
  acct 3 ⊕ raise (acct 4 ⊕ s .realiser .potential) ⊕ (acct 2 ⊕ z .realiser .potential)
recursor z s .realiser .potential-ok = (`acct `⊕ raise-ok (`acct `⊕ s .realiser .potential-ok)) `⊕ (`acct `⊕ z .realiser .potential-ok)
recursor{Γ}{X} z s .realises (γ , n) {n₀} η α v (refl , d) = is-realisable
  where
    η₀ = η ,- v
    η₁ = η₀ ,- clo (body-expr (z .realiser .expr) (s .realiser .expr) n₀) η₀

    loop-potential : ℕ → |M|
    loop-potential n = scale n (acct 4 ⊕ s .realiser .potential) ⊕ (acct 2 ⊕ z .realiser .potential)

    loop : (n : ℕ) → Eval (X (γ , n)) (body-expr (z .realiser .expr) (s .realiser .expr) n₀) (loop-potential n) (η₁ ,- nat-val n)
    loop zero = is-realisable
      where
        r = z .realises γ (η₁ ,- _ ,- _) ∅ ⋆ (identity {∅})

        is-realisable : Eval _ _ _ _
        is-realisable .result = r .result
        is-realisable .steps = 2 + r .steps
        is-realisable .result-potential = r .result-potential
        is-realisable .evaluation = letpair zero (cond-true (suc zero) (r .evaluation))
        is-realisable .result-realises = r .result-realises
        is-realisable .accounted =
          pair (scale-zero (acct 4 ⊕ s .realiser .potential)) ； unit' ； acct⊕- ； unit-inv ； r .accounted
    loop (suc n) = is-realisable
      where
        r-n = loop n
        r-s = s .realises (γ , n) (η₁ ,- _ ,- _ ,- _) (r-n .result-potential) (r-n .result) (r-n .result-realises)

        is-realisable : Eval _ _ _ _
        is-realisable .result = r-s .result
        is-realisable .steps = 3 + r-n .steps + 1 + r-s .steps
        is-realisable .result-potential = r-s .result-potential
        is-realisable .evaluation = letpair zero (cond-false (suc zero) (seq (app (suc (suc (suc zero))) zero (r-n .evaluation)) (r-s .evaluation)))
        is-realisable .result-realises = r-s .result-realises
        is-realisable .accounted =
          weaken (pair (scale-suc n (acct 4 ⊕ s .realiser .potential) (`acct `⊕ s .realiser .potential-ok)) ； assoc-inv ； assoc-inv ； acct⊕- ； pair' (r-n .accounted) ； r-s .accounted)
                 (≤-reflexive (cong (λ □ → suc (suc (suc □))) (cong (λ □ → □ + r-s .steps) (+-comm (loop n .steps) 1))))
           -- Given: k₁ ≤D⟨ loop-potential n , r-n .result-potential ⟩
           --        k₂ ≤D⟨ s .potential ⊕ r-n .result-potential , r-s .result-potential ⟩
           -- 3 + k₁ + 1 + k₁ ≤D⟨ loop-potential (suc n) , r-s .result-potential ⟩
           --
           --  lemma : 0 ≤D⟨ loop-potential (suc n) , acct 3 ⊕ loop-potential n ⊕ acct 1 ⊕ s .potential ⟩

    is-realisable : Eval _ _ _ _
    is-realisable .result = loop n .result
    is-realisable .steps = 3 + loop n .steps
    is-realisable .result-potential = loop n .result-potential
    is-realisable .evaluation = seq lam (app zero (suc zero) (loop n .evaluation))
    is-realisable .result-realises = loop n .result-realises
    is-realisable .accounted =
      pair' d ； assoc-inv ； assoc-inv ； acct⊕- ； pair' symmetry ； assoc ； pair (raise→scale (acct 4 ⊕ s .realiser .potential) n) ； pair (pair' term ； unit) ； loop n .accounted
       -- Given: loop n .steps ≤D⟨ loop-potential n , loop n .result-potential ⟩
       -- 3 + loop n .steps ≤D⟨ γ ⊕ α , loop n .result-potential ⟩
       --                       acct 3 ⊕ raise (acct 4 ⊕ s .potential) ⊕ (acct 2 ⊕ z .potential) ⊕ α
       --                  =3=> raise (acct 4 ⊕ s .potential) ⊕ (acct 2 ⊕ z .potential) ⊕ α
       --                  ===> raise (acct 4 ⊕ s .potential) ⊕ (acct 2 ⊕ z .potential) ⊕ size n
       --                  ===> (raise (acct 4 ⊕ s .potential) ⊕ size n) ⊕ (acct 2 ⊕ z .potential)
       --                  ===> repeat n (acct 4 ⊕ s .potential) ⊕ (acct 2 ⊕ z .potential)
       --                  =k=> loop n .result-potential
