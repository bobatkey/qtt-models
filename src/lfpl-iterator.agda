module lfpl-iterator where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Fin using (Fin; zero; suc)
open import Data.Nat.Properties
open import Data.Product
open import Data.Unit
open import Data.Empty
open import Relation.Binary.PropositionalEquality
open import machine-model
open import resource-monoid
open import cost-model

-- ultimately would like to prove that for any finitary polynomial
-- type we have an initial fixpoint when it is augmented by diamonds.

module lfpl-category (M : rmonoid) (M₀ : sub-monoid M)
                     (open rmonoid using (∣_∣))
                     (open rmonoid M hiding (∣_∣))
                     (size         : ℕ → ∣ M ∣)
                     (raise        : ∣ M ∣ → ∣ M ∣)
                     (raise-ok     : ∀ {α} → M₀ .sub-monoid.member α → M₀ .sub-monoid.member (raise α))
                     (scale        : ℕ → ∣ M ∣ → ∣ M ∣)
                     (raise→scale : ∀ α n → 0 ≤D⟨ raise α ⊕ size n , scale n α ⊕ size n ⟩)
                     (scale-zero   : ∀ α → 0 ≤D⟨ scale zero α , ∅ ⟩)
                     (scale-suc    : ∀ n α → M₀ .sub-monoid.member α → 0 ≤D⟨ scale (1 + n) α , α ⊕ scale n α ⟩)
                     -- one of these two is not possible in the Soft Affine category
                     (size-suc     : ∀ n → 0 ≤D⟨ size (suc n) , size n ⊕ size 1 ⟩)
                     (suc-size     : ∀ n → 0 ≤D⟨ size n ⊕ size 1 , size (suc n) ⟩)
      where

  open resource-category M M₀ public
  open sub-monoid M₀

  `nat : obj
  ∥ `nat ∥ = ℕ
  `nat .realises α v n = v ≡ nat-val n × 0 ≤D⟨ α , size (suc n) ⟩

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
                         seq ⋆ then
                         seq (suc zero , zero) then
                         s (7 + n))

  rec-expr : (z s : ∀ n → exp (1 + n)) → ∀ n → exp (suc n)
  rec-expr z s n = seq (ƛ (body-expr z s n)) then (zero · suc zero)

  recursor : ∀ {X} →
             (z : ◇ ==> X) →
             (s : (X ⊗ ◇) ==> X) →
             (`nat ==> X)
  recursor z s .mor = ℕ-rec (z .mor tt) (λ x → s .mor (x , tt))
  recursor z s .expr = rec-expr (z .expr) (s .expr)
  recursor z s .potential = acct 3 ⊕ raise (acct 8 ⊕ s .potential) ⊕ (acct 2 ⊕ z .potential)
  recursor z s .potential-ok = (`acct `⊕ raise-ok (`acct `⊕ s .potential-ok)) `⊕ (`acct `⊕ z .potential-ok)
  recursor{X} z s .realisable {n₀} η α v n (refl , d) = is-realisable
    where
      η₀ = η ,- v
      η₁ = η₀ ,- clo (body-expr (z .expr) (s .expr) n₀) η₀

      loop-potential : ℕ → ∣ M ∣
      loop-potential n = size (suc n) ⊕ scale n (acct 8 ⊕ s .potential) ⊕ (acct 2 ⊕ z .potential)

      loop : (n : ℕ) → Eval X (body-expr (z .expr) (s .expr) n₀) (loop-potential n) (η₁ ,- nat-val n) (recursor z s .mor n)
      loop zero = is-realisable
        where
          r = z .realisable (η₁ ,- _ ,- _) (size 1) ⋆ tt (identity {size 1})

          is-realisable : Eval _ _ _ _ _
          is-realisable .result = r .result
          is-realisable .steps = 2 + r .steps
          is-realisable .result-potential = r .result-potential
          is-realisable .evaluation = letpair zero (cond-true (suc zero) (r .evaluation))
          is-realisable .result-realises = r .result-realises
          is-realisable .accounted =
            pair (pair' (scale-zero (acct 8 ⊕ s .potential))) ⟫ pair unit ⟫ assoc ⟫ pair symmetry ⟫ assoc-inv ⟫ acct⊕- ⟫ symmetry ⟫ r .accounted
      loop (suc n) = is-realisable
        where
          r-n = loop n
          r-s = s .realisable (η₁ ,- _ ,- _ ,- _ ,- _ ,- _) (r-n .result-potential ⊕ size 1) (r-n .result , ⋆)
                      (recursor z s .mor n , tt)
                      (r-n .result-potential , size 1 , identity , r-n .result-realises , identity)

          is-realisable : Eval _ _ _ _ _
          is-realisable .result = r-s .result
          is-realisable .steps = 3 + r-n .steps + 1 + (2 + (2 + r-s .steps))
          is-realisable .result-potential = r-s .result-potential
          is-realisable .evaluation =
            letpair zero (cond-false (suc zero)
                          (seq (app (suc (suc (suc zero))) zero (r-n .evaluation))
                          (seq mkunit
                          (seq (mkpair (suc zero) zero) (r-s .evaluation)))))
          is-realisable .result-realises = r-s .result-realises
          is-realisable .accounted =
            weaken (pair (pair' (scale-suc n (acct 8 ⊕ s .potential) (`acct `⊕ s .potential-ok))) ⟫
                    pair (pair (size-suc (suc n))) ⟫
                    assoc-inv ⟫
                    pair' assoc-inv ⟫
                    assoc ⟫
                    pair assoc-inv ⟫
                    pair symmetry ⟫
                    assoc-inv ⟫
                    pair' (assoc ⟫ r-n .accounted) ⟫
                    pair symmetry ⟫
                    assoc-inv ⟫
                    assoc-inv ⟫
                    acct⊕- ⟫
                    pair' symmetry ⟫
                    r-s .accounted)
              (begin
                3 + r-n .steps + 1 + (2 + (2 + r-s .steps))
              ≡⟨ solve 2 (λ x y →  con 3 :+ x :+ con 1 :+ (con 2 :+ (con 2 :+ y))
                                 := x :+ con 0 :+ con 0 :+ con 0 :+ con 8 :+ con 0 :+ y) refl (r-n .steps) (r-s .steps) ⟩
                r-n .steps + 0 + 0 + 0 + 8 + 0 + r-s .steps
              ∎)
            where open ≤-Reasoning
                  open import Data.Nat.Solver
                  open +-*-Solver

      is-realisable : Eval _ _ _ _ _
      is-realisable .result = loop n .result
      is-realisable .steps = 3 + loop n .steps
      is-realisable .result-potential = loop n .result-potential
      is-realisable .evaluation = seq lam (app zero (suc zero) (loop n .evaluation))
      is-realisable .result-realises = loop n .result-realises
      is-realisable .accounted =
        (pair' d) ⟫ (assoc-inv ⟫ (assoc-inv ⟫ (acct⊕- ⟫ ((pair' symmetry) ⟫ (assoc ⟫ ((pair (pair' (size-suc n))) ⟫ (pair assoc ⟫ (pair (pair (raise→scale (acct 8 ⊕ s .potential) n)) ⟫ (pair assoc-inv ⟫ (pair (pair' (suc-size n)) ⟫ (pair symmetry ⟫ loop n .accounted)))))))))))
