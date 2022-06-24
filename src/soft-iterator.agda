module soft-iterator where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Fin using (zero; suc)
open import Data.Nat.Properties
open import Data.Product
open import Data.Unit
open import Data.Empty
open import Relation.Binary.PropositionalEquality
open import machine-model
open import resource-monoid
open import cost-model

-- we can augment a resource-category with a natural number iterator
-- if the underlying resource monoid supports some extra things.
module iter-category (M : rmonoid) (M₀ : sub-monoid M)
                     (open rmonoid using (∣_∣))
                     (open rmonoid M hiding (∣_∣))
                     (size         : ℕ → ∣ M ∣)
                     (raise        : ∣ M ∣ → ∣ M ∣)
                     (raise-ok     : ∀ {α} → M₀ .sub-monoid.member α → M₀ .sub-monoid.member (raise α))
                     (scale        : ℕ → ∣ M ∣ → ∣ M ∣)
                     (raise→scale : ∀ α n → 0 ≤D⟨ raise α ⊕ size n , scale n α ⊕ size n ⟩)
                     (scale-zero   : ∀ α → 0 ≤D⟨ scale zero α , ∅ ⟩)
                     (scale-suc    : ∀ n α → M₀ .sub-monoid.member α → 0 ≤D⟨ scale (1 + n) α , α ⊕ scale n α ⟩)
      where

  open resource-category M M₀ public
  open sub-monoid M₀

  `nat : obj
  ∥ `nat ∥ = ℕ
  `nat .realises α v n = v ≡ nat-val n × 0 ≤D⟨ α , size n ⟩

  ◇ : obj
  ∥ ◇ ∥ = ⊤
  ◇ .realises α ⋆         tt = 0 ≤D⟨ α , size 1 ⟩
  ◇ .realises α (_ , _)   tt = ⊥
  ◇ .realises α true      tt = ⊥
  ◇ .realises α false     tt = ⊥
  ◇ .realises α (clo _ _) tt = ⊥

  ℕ-rec : ∀ {A : Set} → A → (A → A) → ℕ → A
  ℕ-rec z s zero    = z
  ℕ-rec z s (suc n) = s (ℕ-rec z s n)

  body-expr : (z s : ∀ n → exp (1 + n)) → ∀ n → exp (3 + n)
  body-expr z s n =
     letpair zero then
     cond suc zero then z (4 + n)
                   else (seq (suc (suc (suc zero)) · zero) then
                         s (5 + n))

  rec-expr : (z s : ∀ n → exp (1 + n)) → ∀ n → exp (suc n)
  rec-expr z s n = seq (ƛ (body-expr z s n)) then (zero · suc zero)

  recursor : ∀ {X} →
             (z : I ==> X) →
             (s : X ==> X) →
             (`nat ==> X)
  recursor z s .mor = ℕ-rec (z .mor tt) (s .mor)
  recursor z s .expr = rec-expr (z .expr) (s .expr)
  recursor z s .potential = acct 3 ⊕ raise (acct 4 ⊕ s .potential) ⊕ (acct 2 ⊕ z .potential)
  recursor z s .potential-ok = (`acct `⊕ raise-ok (`acct `⊕ s .potential-ok)) `⊕ (`acct `⊕ z .potential-ok)
  recursor{X} z s .realisable {n₀} η α v n (refl , d) = is-realisable
    where
      η₀ = η ,- v
      η₁ = η₀ ,- clo (body-expr (z .expr) (s .expr) n₀) η₀

      loop-potential : ℕ → ∣ M ∣
      loop-potential n = scale n (acct 4 ⊕ s .potential) ⊕ (acct 2 ⊕ z .potential)

      loop : (n : ℕ) → Eval X (body-expr (z .expr) (s .expr) n₀) (loop-potential n) (η₁ ,- nat-val n) (recursor z s .mor n)
      loop zero = is-realisable
        where
          r = z .realisable (η₁ ,- _ ,- _) ∅ ⋆ tt (identity {∅})

          is-realisable : Eval _ _ _ _ _
          is-realisable .result = r .result
          is-realisable .steps = 2 + r .steps
          is-realisable .result-potential = r .result-potential
          is-realisable .evaluation = letpair zero (cond-true (suc zero) (r .evaluation))
          is-realisable .result-realises = r .result-realises
          is-realisable .accounted =
            pair (scale-zero (acct 4 ⊕ s .potential)) ⟫ unit' ⟫ acct⊕- ⟫ unit-inv ⟫ r .accounted
      loop (suc n) = is-realisable
        where
          r-n = loop n
          r-s = s .realisable (η₁ ,- _ ,- _ ,- _) (r-n .result-potential) (r-n .result) (recursor z s .mor n) (r-n .result-realises)

          is-realisable : Eval _ _ _ _ _
          is-realisable .result = r-s .result
          is-realisable .steps = 3 + r-n .steps + 1 + r-s .steps
          is-realisable .result-potential = r-s .result-potential
          is-realisable .evaluation = letpair zero (cond-false (suc zero) (seq (app (suc (suc (suc zero))) zero (r-n .evaluation)) (r-s .evaluation)))
          is-realisable .result-realises = r-s .result-realises
          is-realisable .accounted =
            weaken (pair (scale-suc n (acct 4 ⊕ s .potential) (`acct `⊕ s .potential-ok)) ⟫ assoc-inv ⟫ assoc-inv ⟫ acct⊕- ⟫ pair' (r-n .accounted) ⟫ r-s .accounted)
                   (≤-reflexive (cong (λ □ → suc (suc (suc □))) (cong (λ □ → □ + r-s .steps) (+-comm (loop n .steps) 1))))
             -- Given: k₁ ≤D⟨ loop-potential n , r-n .result-potential ⟩
             --        k₂ ≤D⟨ s .potential ⊕ r-n .result-potential , r-s .result-potential ⟩
             -- 3 + k₁ + 1 + k₁ ≤D⟨ loop-potential (suc n) , r-s .result-potential ⟩
             --
             --  lemma : 0 ≤D⟨ loop-potential (suc n) , acct 3 ⊕ loop-potential n ⊕ acct 1 ⊕ s .potential ⟩

      is-realisable : Eval _ _ _ _ _
      is-realisable .result = loop n .result
      is-realisable .steps = 3 + loop n .steps
      is-realisable .result-potential = loop n .result-potential
      is-realisable .evaluation = seq lam (app zero (suc zero) (loop n .evaluation))
      is-realisable .result-realises = loop n .result-realises
      is-realisable .accounted =
        pair' d ⟫ assoc-inv ⟫ assoc-inv ⟫ acct⊕- ⟫ pair' symmetry ⟫ assoc ⟫ pair (raise→scale (acct 4 ⊕ s .potential) n) ⟫ pair (pair' term ⟫ unit) ⟫ loop n .accounted
         -- Given: loop n .steps ≤D⟨ loop-potential n , loop n .result-potential ⟩
         -- 3 + loop n .steps ≤D⟨ γ ⊕ α , loop n .result-potential ⟩
         --                       acct 3 ⊕ raise (acct 4 ⊕ s .potential) ⊕ (acct 2 ⊕ z .potential) ⊕ α
         --                  =3=> raise (acct 4 ⊕ s .potential) ⊕ (acct 2 ⊕ z .potential) ⊕ α
         --                  ===> raise (acct 4 ⊕ s .potential) ⊕ (acct 2 ⊕ z .potential) ⊕ size n
         --                  ===> (raise (acct 4 ⊕ s .potential) ⊕ size n) ⊕ (acct 2 ⊕ z .potential)
         --                  ===> repeat n (acct 4 ⊕ s .potential) ⊕ (acct 2 ⊕ z .potential)
         --                  =k=> loop n .result-potential
